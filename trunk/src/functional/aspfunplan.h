
/* define's */
#define MAXTIME      50
#define MAXINST      (MAXTIME*4)
#define MAXATOMS     500
#define MAXOPERATORS 2000
#define SIZE         (MAXATOMS + 2)


/* struct's and typedef's */
struct operator_s {
  char *name;
  int  (*function)(void);
} operator_s;
typedef struct operator_s *operator_p;


/* extern variables */
extern int curtime;
extern int numoper;
extern int (*opertable[MAXOPERATORS])();
extern struct operator_s  operators[MAXOPERATORS];


/* extern functions */
extern void do_actions (void);
extern void set_initial_situation (void);
extern void fill_table (void);
extern int  have_a_goal (void);

