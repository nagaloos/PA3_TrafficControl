#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <pthread.h>
#include <semaphore.h>
#include <time.h>
#include <sys/time.h>
#include <assert.h>

//IMPORTANT CONSTANTS
#define totalCars 8
#define stopTime 2 //stop for 2 seconds after arrival
#define leftTurn 5.0 //time it takes to travel when allowed to proceed
#define straightThrough 4.0
#define rightTurn 3.0

//IMPORTANT STRUCTS
typedef struct _directions { //hold the origin and destination directions of each car
    char dir_original;
    char dir_target;
} directions;
typedef struct car {
    int cid; //unique car identification
    double arrival_time; //consistency in naming with instruction document
    double crossTime; //how long a car takes to travel
    directions dir; //origin and destination directions
    int startingPoint; //representation of the starting direction of a car: N=^, E=>, S=v, W=<
    unsigned circles; //circles are potential places where cars traveling in different directions can collide
    int lanePosition; //car's position in lane queue
} car;

//TIME MANAGEMENT
//based on https://github.com/remzi-arpacidusseau/ostep-code/blob/master/intro/common.h
static double t0; //when the simulation begins
static double runTime(void) { //calculate how much time has elapsed since the simulation started
    struct timeval t;
    int rc = gettimeofday(&t, NULL);
    assert(rc == 0);
    return (double)t.tv_sec + (double)t.tv_usec / 1e6 - t0; //convert microseconds to seconds
}
//simulate crossing
static void Spin(double sec) {
    double end = runTime() + sec;
    while (runTime() < end)
        ; //do nothing in loop
}

//display a car's ID, original direction, target direction, and action being performed
static void logEvent(car *c, const char *event) {
    printf("Time %.1f: Car %d (%c %c) %s\n", runTime(), c->cid, c->dir.dir_original, c->dir.dir_target, event);
}

//when cars arrive, they have to stop and wait, forming a FIFO queue
typedef struct line_t {
    pthread_mutex_t m;
    int count; //use a ticket system to control when each car can go
    sem_t turn[totalCars + 1]; //turn[n] posted = ticket n may go
} line;
//initialize the queue
static void line_init(line *l) {
    pthread_mutex_init(&l->m, NULL); //initialize mutex variable so it can be used
    l->count = 0; //the lower the int ticket, the higher a car's priority
    for (int i = 0; i <= totalCars; i++)
        sem_init(&l->turn[i], 0, i == 0); //ticket 0 may go immediately
}
//allow cars to join the queue
static int line_join(line *l) {
    pthread_mutex_lock(&l->m); //this lock ensures that two cars get tickets one at a time, in the order they came in
    int n = l->count++; //no two cars in the same lane can be given the same ticket number
    pthread_mutex_unlock(&l->m);
    return n; //give the ticket number
}
static void line_wait(line *l, int n) { //block until a ticket is posted
    sem_wait(&l->turn[n]); 
}
static void line_done(line *l, int n) { //release the next one waiting
    sem_post(&l->turn[n + 1]); 
}
static line lane[4]; //head-of-line lock of each stop sign
static line gate; //control the order in which cars may enter since multiple front cars may be ready, but they're still subject to the rule of one only occupying a certain space

//circles are used to mark out critical sections where car collisions can occur without control
//based on the turning left diagram, each road has an...
//entry point (x4)
//exit point (x4)
//intersection for perpendicular straight travel paths (x4)
//intersection for perpendicular left crossing paths (x4)
//intersection between turning left while the next car clockwise goes straight (x4)
//intersection between turning left while the car with opposite starting orientation goes straight (x4)
//this makes 24 critical points
#define NC 20 //four of the critical points (the entry points) are already taken care of
static sem_t circle_free[NC]; //this is the resource semaphore: if this value is 1, no one is at a circle
static pthread_mutex_t circle_m[NC][4]; //[circle][origin]: a car from an origin direction gets to lock any critical points it crosses as it drives
static int circle_cnt[NC][4]; //cars in the path of critical points per origin

static void circle_enter(int k, int origin) {
    pthread_mutex_lock(&circle_m[k][origin]); //guard circle k and origin point o
    if (circle_cnt[k][origin]++ == 0) //first car in the queue takes the circle space and locks it for others
        sem_wait(&circle_free[k]); //request one unit of space
    pthread_mutex_unlock(&circle_m[k][origin]);
}
static void circle_exit(int k, int origin) {
    pthread_mutex_lock(&circle_m[k][origin]);
    if (--circle_cnt[k][origin] == 0) //last car from a specific origin unlocks the circle space for others
        sem_post(&circle_free[k]); //release a unit of space and wake a waiting thread
    pthread_mutex_unlock(&circle_m[k][origin]);
}

//the intersection looks like this:
//      [][][]   | ^ [][][]
//      [][][]   | N [][][]
//      []STOP   |   STOP[]
//      < W
//      ------       ------
//                      E >
//      []STOP   |   STOP[]
//      [][][] S |   [][][]
//      [][][] v |   [][][]
//circle numbering
//number roads clockwise: 0=N 1=E 2=S 3=W
//(x+1)%4 is the next road clockwise, (x+3)%4 the previous one, (x+2)%4 the opposite one
static int pair(int a, int b) { 
    return b == (a + 1) % 4 ? a : b; 
}  /* 0..3 */

#define EXIT(d) (1u << (0  + (d))) //0-3 exit points
#define SS(a, b) (1u << (4  + pair(a, b))) //4-7 perpendicular straight travel paths
#define LL(a, b) (1u << (8  + pair(a, b))) //8-11 perpendicular left crossing paths
#define SL_SIDE(x) (1u << (12 + (x))) //12-15 straight travel path and a left crossing path from the previous road x-1
#define SL_OPP(x) (1u << (16 + (x))) //16-19 straight travel path and a left crossing path from the opposite road x+2

//all red circles on the path of a car from road x, turn = 0 straight, 1 left, 2 right, going out on road 'to' (entry circle = lane[x])
static unsigned circles_for(int x, int turn, int to) {
    //(x+1)%4 is the next road clockwise, (x+3)%4 the previous one, (x+2)%4 the opposite one
    int nx = (x + 1) % 4, pv = (x + 3) % 4, op = (x + 2) % 4;
    switch (turn) {
    case 0:  return EXIT(to) | SS(x, nx) | SS(x, pv) | SL_SIDE(x) | SL_OPP(x); //as you travel straight, you perpendicularly pass the next and previous roads and remain parallel to your current and opposite one
    case 1:  return EXIT(to) | LL(x, nx) | LL(x, pv) | SL_SIDE(nx) | SL_OPP(op); //as you travel left, you pass critical points created by a potential left crossing from the next and previous roads, as well as those from a potential next or opposite straight crossing
    default: return EXIT(to); //as you travel right, you stay within your quadrant of the intersection
    }
}

//EVENTS
void ArriveIntersection(car *c) {
    logEvent(c, "arriving");
    c->lanePosition = line_join(&lane[c->startingPoint]); //car joins the line
    Spin(stopTime); //car makes its required 2-second stop
    line_wait(&lane[c->startingPoint], c->lanePosition); //force the car to wait until it's at the front

    int g = line_join(&gate); //car obtains ticket at the entry point
    line_wait(&gate, g); //block until high-priority ticket holders let go of their tickets

    for (int k = 0; k < NC; k++) //lock circles it'll cross
        if (c->circles & (1u << k)) //fixed order based on critical point numbers
            circle_enter(k, c->startingPoint); //test if bit k is set

    line_done(&lane[c->startingPoint], c->lanePosition); //next car moves up in the line
    line_done(&gate, g); //next car may try to make a move
}
void CrossIntersection(car *c) {
    logEvent(c, "crossing");
    Spin(c->crossTime); //program waits for a certain amount of time depending on crossing direction
}
void ExitIntersection(car *c) {
    logEvent(c, "exiting");
    for (int k = 0; k < NC; k++) //release circles that were locked
        if (c->circles & (1u << k)) //relase in order of critical points
            circle_exit(k, c->startingPoint);
}

//change Car function so that it can more reliably serve as a superfunction that executes a bunch of smaller ones
static void *Car(void *arg) {
    car *c = arg;
    ArriveIntersection(c);
    CrossIntersection(c);
    ExitIntersection(c);
    return NULL;
}

//each direction has a character and integer code associated with it
static int idx(char ch) {
    if (ch =='^') { //northbound
        return 0;
    }
    else if (ch =='>') { //eastbound
        return 1;
    }
    else if (ch =='v') { //southbound
        return 2;
    }
    else { //westbound, <
        return 3;
    }
}

//      [][][]   | ^ [][][]
//      [][][]   | N [][][]
//      []STOP   |   STOP[]
//      < W
//      ------       ------
//                      E >
//      []STOP   |   STOP[]
//      [][][] S |   [][][]
//      [][][] v |   [][][]
static void init_car(car *c, int cid, double t, char from, char to) { //initialize a car
    int f = idx(from); //assign start orientation 
    int d = idx(to); //assign target orientation
    int diff = (d - f + 4) % 4; //calculate the clockwise angular distance from from to to based on clock directions
    int turn = 0; //initialize variable holding direction code
    if (diff == 0) //making a straight drive doesn't use any turns
    {
        turn = 0;
    }
    else if (diff == 1) //making a right turn involves moving to the next direction on a compass clockwise
    {
        turn = 2;
    }
    else if (diff == 3) //making a left turn involves moving three clockwise steps to the target direction
    {
        turn = 1;
    }
    else //taking two clockwise steps makes you face the opposite direciton, implying a U-turn
    {
        fprintf(stderr, "U-turns aren't allowed");
        exit(1);
    }

    c->cid = cid;
    c->arrival_time = t;
    c->dir = (directions){ from, to };
    c->startingPoint = f;
    c->circles = circles_for(f, turn, d);
    if (turn == 0) { //before assigning a car's crossing time, look at the its directions
        c->crossTime = straightThrough;
    }
    else if (turn == 1) {
        c->crossTime = leftTurn;
    }
    else {
        c->crossTime = rightTurn;
    }
}

int main(void) {
    //print my username
    printf("nagaloos");
    //initialize cars using information from given table
    static const struct { double t; char from, to; } table[totalCars] = {
        {1.1,'^','^'}, {2.2,'^','^'}, {3.3,'^','<'}, {4.4,'v','v'},
        {5.5,'v','>'}, {6.6,'^','^'}, {7.7,'>','^'}, {8.8,'<','^'},
    };
    car cars[totalCars]; //initialize car struct
    pthread_t tid[totalCars]; //initialize threading

    for (int i = 0; i < 4; i++) {
        line_init(&lane[i]); //initialize each road
    }
    line_init(&gate); //initialize the head gatekeeping mechanism
    for (int k = 0; k < NC; k++) {
        sem_init(&circle_free[k], 0, 1); //initialize collision points
        for (int o = 0; o < 4; o++)
            pthread_mutex_init(&circle_m[k][o], NULL); //initialize locks securing red circle zones
    }

    //start timing and record the seconds at important events
    struct timeval t;
    int rc = gettimeofday(&t, NULL);
    assert(rc == 0);
    t0 = (double) t.tv_sec + (double) t.tv_usec / 1e6; //convert microseconds to seconds

    for (int i = 0; i < totalCars; i++) { //when this program runs, it starts off as one process
        init_car(&cars[i], i + 1, table[i].t, table[i].from, table[i].to); //fill in information about each car
        Spin(cars[i].arrival_time - runTime()); //make a car wait at its origin road
        pthread_create(&tid[i], NULL, Car, &cars[i]); //split the process into threads and simulate crossing
    }
    for (int i = 0; i < totalCars; i++)
        pthread_join(tid[i], NULL); //after each thread finishes, join them all together
    
    return 0;
}