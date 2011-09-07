/* Prologue for generated code -- DO NOT MODIFY!!! */

/* struct's and typedef's */
struct reference_s
{
  FSET time[MAXTIME];
} reference_s;

struct present_s
{
  int prst;
  int cost;
} present_s;

struct pinstant_s
{
  int prec[20];
  int time[20];
} pinstant_s;


/* static global variables */
static struct reference_s delete[SIZE], support[SIZE];
static struct present_s present[SIZE][MAXTIME];
static struct pinstant_s prectime[MAXINST];
static int time[SIZE], ptime = 0;


void
start (register literal_p sit)
{
  register struct reference_s *p;
  register literal_p ip;
  register int at = 1;
    
  curtime = 0;
  memset (time, 0, sizeof(int)*MAXATOMS);
  memset (delete, 0, sizeof(struct reference_s)*MAXATOMS);
  memset (present, 0, sizeof(struct present_s)*MAXATOMS*MAXTIME);

  for (ip = &sit[1]; ip < &sit[SIZE]; ip++, at++)
    {
      if (ip->lit)
        present[at][curtime].prst = 1;
      else
        present[at][curtime].prst = 0;
      present[at][curtime].cost = 0;
    }

  for (p = &delete[1]; p < &delete[SIZE]; p++)
    fcopy(emptyset, p->time[0]);

  for (p = &support[1]; p < &support[SIZE]; p++)
    fcopy(emptyset, p->time[0]);
}


void
check_preconds (register int *prec, register int *curr, int ctime)
{
  register int tm = 0, found = 0, *jp, c, *pp, *tp;
  register struct present_s *ip;


  if (!*curr)
    {
      for (c = 0, jp = prec; *jp; jp++)
	c += (time[*jp] == (ctime - 1));
      
      if (!c || ptime)
        return;
      
      pp = &prectime[ptime].prec[0];
      tp = &prectime[ptime].time[0];
      for (jp = prec; *jp; jp++)
	{
	  *(pp++) = *jp;
	  *(tp++) = time[*jp];
	}
      *pp = 0;
      *tp = 0;
      ptime++;
    }
  else
    {
      for (ip = present[*curr]; ip < &present[*curr][curtime]; ip++, tm++)
        if (ip->prst && !ptime)
          {
	    time[*curr] = tm;
	    check_preconds (prec, curr + 1, ctime);
          }
    }
}


int
next_preconds (void)
{
  register int *pp, *tp;

  if (ptime)
    {
      --ptime;
      pp = &prectime[ptime].prec[0];
      tp = &prectime[ptime].time[0];
      while (*pp)
	time[*(pp++)] = *(tp++);
      return 1;
    }
  else
    return 0;
}


void
clean (register int time)
{
  register int i;
  register struct reference_s *p;
 
  for (i = 0; i < SIZE; i++)
    {
      present[i][time].prst = 0;
      present[i][time].cost = 9999;
    }

  for (p = &delete[1]; p < &delete[SIZE]; p++)
    fcopy(emptyset, p->time[time]);

  for (p = &support[1]; p < &support[SIZE]; p++)
    fcopy(emptyset, p->time[time]);
}
