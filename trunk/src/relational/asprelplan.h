
/* define's */
#define MAXTIME      35
#define MAXINST      (MAXTIME*4)
#define MAXATOMS     500
#define MAXOPERATORS 2000
#define SIZE         (MAXATOMS + 2)


/* struct's and typedef's */
struct literal_s 
{
  int  lit;
  int  cost;
} literal_s;

struct operator_s {
  char *name;
  int  prc[10];
  int  add[10];
  int  del[10];
  int  (*function)(void);
} operator_s;

typedef struct literal_s  *literal_p;
typedef struct operator_s *operator_p;


/* extern variables */
extern struct literal_s situation[SIZE];
extern struct literal_s new_situation[SIZE];
extern int curtime;

extern struct operator_s  operators[MAXOPERATORS];

extern int (*opertable[MAXOPERATORS])();
extern int numoper;


/* extern functions */
extern void do_actions (void);
extern void set_initial_situation (void);
extern int  goal_situation (literal_p);
extern void fill_table (void);
extern void start (literal_p);
extern void fill_primes (void);
extern int  have_a_goal (void);

