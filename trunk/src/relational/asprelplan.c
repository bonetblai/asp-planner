#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <sys/types.h>
#include <math.h>
#include <time.h>
#include "asprelplan.h"


/* define's */
#define BSIZE            (sizeof(struct literal_s) * SIZE)
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
  struct literal_s   situation[SIZE];
  struct hashentry_s *next;
} hashentry_s;
typedef struct hashentry_s *hashentry_p;

struct offspring_s
{
  struct literal_s sit[SIZE];
  int op;
  int rop;
  struct hashentry_s *hentry;
} offspring_s;
typedef struct offspring_s *offspring_p;


/* global variables */
static int          cutoff = 100, lookahead = 1;
static int          branch = 15, debug = 0, updates = 0;
static int          depth = 2, iterations = 40;
static float        Xfactor = 1;

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
static int          (*hfunction)(register literal_p);


/* global extern variables */
int                curtime;
int                numoper;
offspring_p        offspring, frontier;
struct literal_s   situation[SIZE];
struct literal_s   new_situation[SIZE];
struct operator_s  operators[MAXOPERATORS];
operator_p         operset[MAXOPERATORS];
int                (*opertable[MAXOPERATORS])();


int
sitcmp (register literal_p sit1, register literal_p sit2)
{
  literal_p sp1 = sit1, sp2 = sit2;

  while (sp1 < &sit1[SIZE] && (sp1++)->lit == (sp2++)->lit);
  return !(sp1 == &sit1[SIZE]);
}


unsigned 
hashf (register literal_p sit)
{
  register literal_p sp = sit;
  register int       *hp = hashvalues;
  register unsigned  val = 0;

  while (sp < &sit[SIZE])
    {
      val += sp->lit ? *hp : 0;
      sp++;
      hp++;
    }
  return (val % HASHSIZE);
}


hashentry_p
read_hash (register literal_p sit)
{
  register hashentry_p entry;

  for (entry = hashtable[hashf (sit)]; entry; entry = entry->next)
    {
      if (!sitcmp (sit, entry->situation))
	return entry;
    }
  return NULL;
}


hashentry_p
insert_hash (register literal_p sit, register float cval, register float hval)
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
      memcpy (entry->situation, sit, BSIZE);
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
update_value (register literal_p sit, register hashentry_p he, register float inc)
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
hvalue (register literal_p sit)
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
heuristic1 (register literal_p sit)
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

  if (curtime == MAXTIME)
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
  frontier = (offspring_p) calloc (offsize, sizeof(struct offspring_s));
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
  register int tsteps, iters, f, op;
  register float cost;
  register hashentry_p he;
  struct literal_s actual_situation[SIZE];
  
  /* initialization */
  memset (situation, 0, BSIZE);
  set_initial_situation ();
  memcpy (actual_situation, situation, BSIZE);
  he = hvalue (situation);
  printf ("initial value = %f\n", COST(he));
  steps = 0;
  f = iters = tsteps = 0;

  /* search */
  while (!goal_situation (actual_situation))
    {
      /* expand a situation */
      j = 0;
      for (i = 1; operators[i].function; i++)
	{
	  memcpy (new_situation, situation, BSIZE);
	  if ((*operators[i].function)())
	    {
	      if (j == offsize)
		{
		  fprintf (stderr, "error: not enough room for offspring\n");
		  fprintf (stderr, "       increment branch value with -b flag "
			   "(current value is %d)\n", branch);
		  exit (-1);
		}
	      memcpy (&(offspring[j].sit), new_situation, BSIZE);
	      offspring[j].op = (!tsteps ? i : op);
	      offspring[j].rop = i;
              j++;
	    }
	}

      /* check for dead-ends */
      if (j == 0)
	{
	  fprintf (stderr, "error: no operator available\n");
	  exit (-1);
	}
      branching += j;

      /* compute the heuristic for the offspring */
      for (i = 0; i < j; i++)
	{
          he = offspring[i].hentry = hvalue (&(offspring[i].sit));
          heuristic[i].hentry = he;
          heuristic[i].idx = i;
	  
	  if (debug > 2)
	    fprintf (stderr, "cost of situation is %f\n", COST(heuristic[i].hentry));
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
      op = offspring[i].op;
      update_value (situation, offspring[i].hentry, 1);

      /* execute the action */
      if (debug > 1)
	fprintf (stderr, "--->  %d %s\n", steps + 1, operators[offspring[i].rop].name);
      memcpy (situation, &(offspring[i].sit), BSIZE);

      /* increment steps */
      stepsdone++;
      if ((++tsteps < depth) && !goal_situation (situation))
	continue;
      else
	{
	  if (&frontier[f] == &frontier[iterations])
	    {
	      fprintf (stderr, "unexpected frontier overfill.\n");
	      exit (-1);
	    }
	  memcpy (&frontier[f++], &offspring[i], sizeof(struct offspring_s));
	  memcpy (situation, actual_situation, BSIZE);
	  iters++;
	  tsteps = 0;
	}

      /* iteration control */
      if (iters < iterations)
	continue;
	  
      /* online execution */
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

      /* execute the action */
      i = heuristic[best].idx;
      fprintf (stderr, "EXECUTE --->  %d %s\n", steps + 1, operators[frontier[i].op].name);
      memcpy (situation, actual_situation, BSIZE);
      memcpy (new_situation, situation, BSIZE);
      (*operators[frontier[i].op].function)();
      memcpy (situation, new_situation, BSIZE);
      memcpy (actual_situation, situation, BSIZE);
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
  memset (situation, 0, BSIZE);
  set_initial_situation ();
  he = hvalue (situation);
  printf ("initial value = %f\n", COST(he));
  steps = 0;
       

  /* search */
  while (!goal_situation (situation))
    {
      /* expand a situation */
      j = 0;
      for (i = 1; operators[i].function; i++)
	{
	  memcpy (new_situation, situation, BSIZE);
	  if ((*operators[i].function)())
	    {
	      if (j == offsize)
		{
		  fprintf (stderr, "error: not enough room for offspring\n");
		  fprintf (stderr, "       increment branch value with -b flag "
			   "(current value is %d)\n", branch);
		  exit (-1);
		}
	      memcpy (&(offspring[j].sit), new_situation, BSIZE);
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
      update_value (situation, offspring[i].hentry, 1);


      /* execute the action */
      if (debug > 1)
        fprintf (stderr, "--->  %d %s\n", steps + lookahead, operators[offspring[i].op].name);
      memcpy (situation, offspring[i].sit, BSIZE);
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
print_help (char *progname)
{
  fprintf (stderr, "Solver for %s problem. Options:\n"
	   "\t-b <n>\tAllow a maximum of <n> sons for a node (default: 15).\n"
	   "\t-c <n>\tSolution length cutoff (default: 100).\n"
	   "\t-d <n>\tDebug level <n> (defualt: 0).\n"
	   "\t-h    \tThis help.\n"
	   "\t-l    \tSolve the problem with Korf's LRTA*.\n"
	   "\t-n <n>\tSolve the problem <n> times.\n"
	   "\t-r <n>\tSet the random seed to <n>.\n"
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
  iters = 1;
  seed1 = 100;
  seed2[0] = seed2[1] = seed2[2] = 100;


  /* check the usage */
  if (argc > 15)
    {
    usage:
      fprintf (stderr, "usage: %s [-b <n>] [-c <n>] [-d <n>] [-h] "
	       "[-l] [-n <n>] [-r <n>] [-X <n>]\n", progname);
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
      case 'r':
	seed2[0] = seed2[1] = seed2[2] = (unsigned short) atoi (*++argv);
	seed1 = (long) seed2[0];
        srand48 (seed1);
        seed48 (seed2);
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
  printf ("\t-r = %d\n", seed2[0]);
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
