#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <sys/types.h>
#include <math.h>
#include <time.h>
#include <aspfunplan.h>
#define IMPORT extern
#include INCFILE


/* define's */
#define SITUATION        (&I_STATE)
#define NEW_SITUATION    (&N_STATE)

#define BSIZE            (sizeof(struct STATE_s))
#define HASHSIZE         200000
#define CLAIMSIZE        5000

#define MIN(x,y)         ((x) > (y) ? (y) : (x))
#define MAX(x,y)         ((x) > (y) ? (x) : (y))
#define COST(p)          ((p)->cvalue + (p)->hvalue)


/* struct's and typedef's */
struct heuristic_s
{
  int idx;
  float val;
  int depth;
  struct hashentry_s *hentry;
} heuristic_s;
typedef struct heuristic_s *heuristic_p;

struct hashentry_s
{
  float cvalue;
  float hvalue;
  struct STATE_s situation;
  struct hashentry_s *next;
} hashentry_s;
typedef struct hashentry_s *hashentry_p;

struct offspring_s
{
  int op;
  int rop;
  struct STATE_s sit;
  struct hashentry_s *hentry;
} offspring_s;
typedef struct offspring_s *offspring_p;


/* global variables */
static int          cutoff = 100, lookahead = 1;
static int          branch = 15, debug = 0, updates = 0;
static int          depth = 2, iterations = 40;
static float        Xfactor = 1;
static int          alarm = 0, noise = 0;
static unsigned int usecs = 0;

static hashentry_p  hashtable[HASHSIZE];
static int          hashdiameter[HASHSIZE];
static int          hashvalues[HASHSIZE];
static int          hashnumelem = 0;
static hashentry_p  hashpool, poolboundary;
static heuristic_p  heuristic;
static int          heurvals = 0, hits = 0, offsize = 1;
static int          steps;
static float        branching = 0, stepsdone = 0, ties = 0;
static time_t       ttime;
static int          (*hfunction)(register STATE_p);


/* global extern variables */
int                curtime;
int                numoper;
offspring_p        offspring, frontier;
struct operator_s  operators[MAXOPERATORS];
operator_p         operset[MAXOPERATORS];
int                (*opertable[MAXOPERATORS])();


unsigned 
hashf (register STATE_p sit)
{
  register int i;
  register char *pc;
  register unsigned  val = 0;

  for (i = 0, pc = (char *) sit; pc < ((char *)sit + BSIZE); pc++, i++)
    val += hashvalues[(*pc * i) % HASHSIZE];
  return (val % HASHSIZE);
}


hashentry_p
read_hash (register STATE_p sit)
{
  register hashentry_p entry;

  for (entry = hashtable[hashf (sit)]; entry; entry = entry->next)
    {
      if (!memcmp (sit, &entry->situation, BSIZE))
	return entry;
    }
  return NULL;
}


hashentry_p
insert_hash (register STATE_p sit, register float cval, register float hval)
{
  register unsigned hf;
  register hashentry_p entry;

  if (!(entry = read_hash (sit)))
    {
      hf = hashf (sit);
      if (hashpool > poolboundary)
	{
	  hashpool = (hashentry_p) malloc (CLAIMSIZE * sizeof(struct hashentry_s));
	  if (!hashpool)
	    {
	      fprintf (stderr, "error: no more memory\n");
	      exit (-1);
	    }
	  poolboundary = &hashpool[CLAIMSIZE-1];
	}
      entry = hashpool++;
      memcpy (&entry->situation, sit, BSIZE);
      entry->cvalue = cval;
      entry->hvalue = hval;
      entry->next = hashtable[hf];
      hashtable[hf] = entry;
      hashnumelem++;
      hashdiameter[hf]++;
    }
  else
    {
      entry->cvalue = cval;
      entry->hvalue = hval;
    }
  return entry;
}


void
hashstat (void)
{
  int *p, max = 0, total = 0, entries = 0;

  for (p = hashdiameter; p != &hashdiameter[HASHSIZE]; p++)
    {
      total += *p;
      if (*p > max)
	max = *p;
      entries += *p ? 1 : 0;
    }

  printf ("\n");
  printf ("total time = %ld\n", ttime);
  printf ("number of elements in hash table = %d\n", hashnumelem);
  printf ("diameter of hash table = %d\n", max);
  if (entries)
    printf ("average length of each hash entry = %f\n", 
	    (float) total / (float) entries);
  printf ("heuristic evaluations = %d\n", heurvals);
  printf ("hits on hash table = %d\n", hits);
  printf ("updates of entries in the hash table = %d\n", updates);
  if (stepsdone)
    {
      printf ("branching factor = %f\n", branching / stepsdone);
      printf ("average number of ties = %f\n", ties / stepsdone);
    }
}


void
update_value (register STATE_p sit, register hashentry_p he, register float inc)
{
  register hashentry_p p;

  if ((p = read_hash (sit)))
    {
      if (p == he)
	p->cvalue += inc;
      else
	{
	  p->hvalue = he->hvalue;
	  p->cvalue = he->cvalue + inc;
	}
      updates++;
    }
  else
    {
      p = insert_hash (sit, -1, -1);
      p->hvalue = he->hvalue;
      p->cvalue = he->cvalue + inc;
    }
}


hashentry_p 
hvalue (register STATE_p sit)
{
  register hashentry_p entry;
  register float cost;

  if ((entry = read_hash (sit)))
    {
      hits++;
      cost = COST(entry);
    }
  else
    {
      cost = (float) (*hfunction)(sit) * Xfactor;
      entry = insert_hash (sit, (float) 0, (float) cost);
    }
  return entry;
}


int
heuristic1 (register STATE_p sit)
{
  register int cost;

  heurvals++;
  curtime = 0;
  start (sit);

  while (curtime < MAXTIME && !(cost = have_a_goal ()))
    {
      curtime++;
      do_actions ();
    }

  if (!alarm && curtime == MAXTIME)
    {
      fprintf (stderr, "error: maxtime slots reached\n");
      fprintf (stderr, "       change MAXTIME value and recompile\n");
      exit (-1);
    }
  else
    --cost;

  return cost;
}


void
initialize (void)
{
  register int i;

  for (i = 0; i < lookahead; i++)
    offsize *= branch;
  offspring = (offspring_p) calloc (offsize, sizeof(struct offspring_s));
  frontier = (offspring_p) calloc (iterations + 1, sizeof(struct offspring_s));
  heuristic = (heuristic_p) calloc (offsize, sizeof(struct heuristic_s));

  memset (&hashdiameter, 0, sizeof(int) * HASHSIZE);
  memset (&hashtable, 0, sizeof(hashentry_p) * HASHSIZE);
  for (i = 0; i < HASHSIZE; i++)
    hashvalues[i] = lrand48 ();
  hashpool = (hashentry_p) calloc (CLAIMSIZE, sizeof(struct hashentry_s));

  if (!hashpool || !heuristic || !offspring || !frontier)
    {
      fprintf (stderr, "error: not enough memory\n");
      exit (-1);
    }
  poolboundary = &hashpool[CLAIMSIZE-1];
  fill_table ();
  printf ("successful initialization\n");
}


int
compare (register const void *e1, register const void *e2)
{
  register float val;
  register heuristic_p h1 = (heuristic_p) e1, h2 = (heuristic_p) e2;

  val = COST(h1->hentry) - COST(h2->hentry);
  return val > 0 ? (int) 1 : (val < 0 ? (int) -1 : (int) 0);
}


int
search_2 (void)
{
  register int i, j, k;
  register int best;
  register int tsteps, iters, f, op, no_frontier = 0;
  register float cost;
  register hashentry_p he;
  static struct STATE_s actual_situation;
  
  /* initialization */
  memset (SITUATION, 0, BSIZE);
  set_initial_situation ();
  memcpy (&actual_situation, SITUATION, BSIZE);
  he = hvalue (SITUATION);
  printf ("initial value = %f\n", COST(he));
  steps = 0;
  f = iters = tsteps = 0;

  /* search */
  while (!goal_situation (&actual_situation))
    {
      /* set the timer */
      ualarm (usecs, 0);
  
      /* expand a situation */
      j = 0;
      for (i = 1; operators[i].function && !alarm; i++)
	{
	  memcpy (NEW_SITUATION, SITUATION, BSIZE);
	  if ((*operators[i].function)())
	    {
	      if (j == offsize)
		{
		  fprintf (stderr, "error: not enough room for offspring\n");
		  fprintf (stderr, "       increment branch value with -b flag "
			   "(current value is %d)\n", branch);
		  exit (-1);
		}
	      memcpy (&(offspring[j].sit), NEW_SITUATION, BSIZE);
	      offspring[j].op = (!tsteps ? i : op);
	      offspring[j].rop = i;
              j++;
	    }
	}

      /* check alarm */
      if (alarm)
	goto online;

      /* check for dead-ends */
      if (j == 0)
	{
	  fprintf (stderr, "error: no operator available\n");
	  exit (-1);
	}
      branching += j;

      /* compute the heuristic for the offspring */
      for (i = 0; i < j && !alarm; i++)
	{
          he = offspring[i].hentry = hvalue (&(offspring[i].sit));
          heuristic[i].hentry = he;
          heuristic[i].idx = i;
	  
	  if (debug > 2)
	    fprintf (stderr, "cost of situation is %f\n", COST(heuristic[i].hentry));
	}

      /* check alarm */
      if (alarm)
	goto online;
      
      /* search for the best (random ties) */
      qsort (heuristic, j, sizeof(struct heuristic_s), compare);
      for (i = 0; (i < j) && (COST(heuristic[i].hentry) == COST(heuristic[0].hentry)); i++);
      best = lrand48() % i;
      ties += i;

      if (debug > 1)
	fprintf (stderr, "%d ties of %d with cost %f (avg. cost = %f)\t", 
		 i, j, COST(heuristic[best].hentry), cost / (float) j);

      /* check alarm */
      if (alarm)
	goto online;
            
      /* update heuristic value */ 
      i = heuristic[best].idx;
      op = offspring[i].op;
      update_value (SITUATION, offspring[i].hentry, 1);

      /* execute the action */
      if (debug > 1)
	fprintf (stderr, "--->  %d %s\n", steps + 1, operators[offspring[i].rop].name);
      memcpy (SITUATION, &(offspring[i].sit), BSIZE);

      /* increment steps */
      stepsdone++;
      if ((++tsteps < depth) && !goal_situation (SITUATION))
	continue;
      else
	{
	  if (&frontier[f] == &frontier[iterations])
	    {
	      fprintf (stderr, "unexpected frontier overfill.\n");
	      exit (-1);
	    }
	  memcpy (&frontier[f++], &offspring[i], sizeof(struct offspring_s));
	  memcpy (SITUATION, &actual_situation, BSIZE);
	  iters++;
	  tsteps = 0;
	}

      /* iteration control */
      if (iters < iterations)
	continue;
	  
      /* online execution */
    online:
      if (!f)
	{
	  /* we only can reach here when the time window was so little
	     that we don't have any node in frontier. Just insert the
	     first operator we find
	     */
	  for (i = 1; operators[i].function; i++)
	    {
	      memcpy (NEW_SITUATION, &actual_situation, BSIZE);
	      if ((*operators[i].function)())
		{
		  memcpy (&(frontier[0].sit), NEW_SITUATION, BSIZE);
		  frontier[0].op = i;
		  break;
		}
	    }
	  f = 1;
	  no_frontier = 1;
	}

      /* setup for sorting */
      for (i = 0; i < f; i++)
        {
          he = frontier[i].hentry = hvalue (&(frontier[i].sit));
          heuristic[i].hentry = he;
          heuristic[i].idx = i;
        }
      qsort (heuristic, f, sizeof(struct heuristic_s), compare);
      for (i = 0; (i < f) && (COST(heuristic[i].hentry) == COST(heuristic[0].hentry)); i++);
      best = lrand48() % i;
      ties += i;

      /* apply noise */
      if (noise > 0)
        if ((float) drand48() < noise)
          {
            for (j = 0, i = 1; operators[i].function; i++)
              {
                memcpy (NEW_SITUATION, &actual_situation, BSIZE);
                if ((frontier[heuristic[best].idx].op != best) && (*operators[i].function)())
                  {
                    memcpy (&(frontier[j].sit), NEW_SITUATION, BSIZE);
                    frontier[j].op = i;
                    j++;
                  }
              }
            best = 0;
            heuristic[best].idx = lrand48() % j;
          }

      /* update heuristic value */ 
      if (no_frontier)
	{
	  i = heuristic[best].idx;
	  update_value (SITUATION, frontier[i].hentry, 1);
	  no_frontier = 0;
	}
      
      /* execute the action */
      i = heuristic[best].idx;
      fprintf (stderr, "EXECUTE --->  %d %s\n", steps + 1, operators[frontier[i].op].name);
      memcpy (SITUATION, &actual_situation, BSIZE);
      memcpy (NEW_SITUATION, SITUATION, BSIZE);
      (*operators[frontier[i].op].function)();
      memcpy (SITUATION, NEW_SITUATION, BSIZE);
      memcpy (&actual_situation, SITUATION, BSIZE);
      steps++;

      /* check cutoff */
      if (steps > cutoff)
	{
	  fprintf (stderr, "no solution found after %d steps\n", steps);
	  return 0;
	}

      /* reset offline */
      iters = 0;
      f = 0;
      alarm = 0;
    }

  /* return */
  return 1;
}


int
search (void)
{
  register int i, j, k, best;
  register float cost;
  register hashentry_p he;


  /* initialization */
  memset (SITUATION, 0, BSIZE);
  set_initial_situation ();
  he = hvalue (SITUATION);
  printf ("initial value = %f\n", COST(he));
  steps = 0;

  
  /* search */
  while (!goal_situation (SITUATION))
    {
      /* expand a situation */
      j = 0;
      for (i = 1; operators[i].function && !alarm; i++)
	{
	  memcpy (NEW_SITUATION, SITUATION, BSIZE);
	  if ((*operators[i].function)())
	    {
	      if (j == offsize)
		{
		  fprintf (stderr, "error: not enough room for offspring\n");
		  fprintf (stderr, "       increment branch value with -b flag "
			   "(current value is %d)\n", branch);
		  exit (-1);
		}
	      memcpy (&(offspring[j].sit), NEW_SITUATION, BSIZE);
	      offspring[j].op = offspring[j].rop = i;
              j++;
	    }
	}
      if (debug > 1)
	fprintf (stderr, "%d possible operators\n", j);
      

      /* check for dead-ends */
      if (j == 0)
	{
	  fprintf (stderr, "error: no operator available\n");
	  exit (-1);
	}
      branching += j;


      /* compute the heuristic for the frontier */
      for (cost = 0, i = 0; i < j; i++)
        {
          /* cost and indexes */
          he = offspring[i].hentry = hvalue (&(offspring[i].sit));
          heuristic[i].hentry = he;
          cost += COST(he);
          heuristic[i].idx = i;

          if (debug > 2)
            fprintf (stderr, "cost of situation is %f\n", COST(he));
        }


      /* search for the best (random ties) */
      qsort (heuristic, j, sizeof(struct heuristic_s), compare);
      for (i = 0; (i < j) && (COST(heuristic[i].hentry) == COST(heuristic[0].hentry)); i++);
      best = lrand48() % i;
      ties += i;

      if (debug > 1)
	fprintf (stderr, "%d ties of %d with cost %f (avg. cost = %f)\t", 
		 i, j, COST(heuristic[best].hentry), cost / (float) j);

      /* update heuristic value */ 
      i = heuristic[best].idx;
      update_value (SITUATION, offspring[i].hentry, 1);


      /* execute the action */
      if (debug > 1)
        fprintf (stderr, "--->  %d %s\n", steps + lookahead, operators[offspring[i].op].name);
      memcpy (SITUATION, &(offspring[i].sit), BSIZE);
      stepsdone++;
      steps++;


      /* check cutoff */
      if (steps > cutoff)
	{
	  fprintf (stderr, "no solution found after %d steps\n", steps);
	  return 0;
	}
    }


  /* return */
  return 1;
}


void
handler1 (int s)
{
  fprintf (stderr, "\nerror: program interrupted by user, exiting...\n");
  hashstat ();
  exit (-1);
}


void
handler2 (int s)
{
  fprintf (stderr, "\ninfo: requested from user\n");
  hashstat ();
}


void
handler3 (int s)
{
  ualarm (0, 0);
  alarm = 1;
}


void
print_help (char *progname)
{
  fprintf (stderr, "Solver for %s problem. Options:\n"
	   "\t-b <n>\tAllow a maximum of <n> sons for a node (default: 15).\n"
	   "\t-c <n>\tSolution length cutoff (default: 100).\n"
	   "\t-d <n>\tDebug level <n> (defualt: 0).\n"
	   "\t-h    \tThis help.\n"
	   "\t-l    \tSolve the problem with Korf's LRTA*.\n"
	   "\t-n <n>\tSolve the problem <n> times.\n"
	   "\t-p <n>\tAdd a perturbation factor of <n>.\n"
	   "\t-r <n>\tSet the random seed to <n>.\n"
	   "\t-t <n>\tSet a time-limit of <n> microseconds for taking a decision.\n"
	   "\t-X <n>\tScale the heuristic with a factor of <n>.\n",
	   progname);
}


int
main (int argc, char **argv)
{
  int iters;
  int (*sfunction)();
  time_t etime;
  char *progname;
  long seed1;
  unsigned short seed2[3];


  /* set some defaults */
  sfunction = search_2;
  hfunction = heuristic1;
  progname = argv[0];
  sigset (SIGINT, handler1);
  sigset (SIGTSTP, handler2);
  sigset (SIGALRM, handler3);
  iters = 1;
  seed1 = 100;
  seed2[0] = seed2[1] = seed2[2] = 100;


  /* check the usage */
  if (argc > 19)
    {
    usage:
      fprintf (stderr, "usage: %s [-b <n>] [-c <n>] [-d <n>] [-h] "
	       "[-l] [-n <n>] [-p <n>] [-r <n>] [-t <n>] [-X <n>]\n", progname);
      exit (-1);
    }


  /* parse options */
  while (argc > 1 && *(*++argv) == '-')
    {
      switch ((*argv)[1])
      {
      case 'b':
	branch = atoi (*++argv);
	argc--;
	break;
      case 'c':
	cutoff = atoi (*++argv);
	argc--;
	break;
      case 'd':
	debug = atoi (*++argv);
	argc--;
	break;
      case 'h':
	print_help (progname);
	exit (0);
	break;
      case 'l':
        sfunction = search;
        break;
      case 'n':
	iters = atoi (*++argv);
	argc--;
	break;
      case 'p':
	noise = (float) atof (*++argv);
	argc--;
	break;
      case 'r':
	seed2[0] = seed2[1] = seed2[2] = (unsigned short) atoi (*++argv);
	seed1 = (long) seed2[0];
        srand48 (seed1);
        seed48 (seed2);
	argc--;
	break;
      case 't':
	usecs = (unsigned) strtol (*++argv, NULL, 10);
	argc--;
	break;
      case 'X':
	Xfactor = (float) atof (*++argv);
	argc--;
	break;
      default:
	goto usage;
	break;
      }
      argc--;
    }
  if (argc != 1)
    goto usage;


  /* let's go for the goal */
  ttime = 0;
  initialize ();
  printf ("running %s with the following args:\n", progname);
  printf ("\t-b = %d\n", branch);
  printf ("\t-c = %d\n", cutoff);
  printf ("\t-d = %d\n", debug);
  if (sfunction == search)
    printf ("\t-l\n");
  printf ("\t-n = %d\n", iters);
  printf ("\t-p = %f\n", noise);
  printf ("\t-r = %d\n", seed2[0]);
  printf ("\t-t = %lu\n", usecs);
  printf ("\t-X = %f\n\n", Xfactor);
  
  do 
    {
      etime = time (NULL);
      
      if ((*sfunction)())
	printf ("solution found in %d steps ", steps);

      etime = time (NULL) - etime;
      ttime += etime;
      printf ("(etime = %ld)\n", (long) etime);
    }
  while (--iters);
  hashstat ();
  return 0;
}
