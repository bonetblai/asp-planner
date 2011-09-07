#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "fset.h"


/* prototypes */
void  finit   (void);
void  funion  (register FSET, register FSET, register FSET);
void  finter  (register FSET, register FSET, register FSET);
void  fins    (register unsigned short, register FSET, register FSET);
void  fdel    (register unsigned int, register FSET, register FSET);
int   fcmp    (register FSET, register FSET);
int   fcomm   (register FSET, register FSET);
void  fucost  (register unsigned short, register FSET, register FSET);
void  fbcost  (register unsigned short, register FSET, register FSET);
short fcost   (register FSET, register FSET);
short focost  (register FSET, register FSET);
int   feother (register unsigned int, register FSET);
short ffirst  (register FSET);
void  fout    (register FILE *, register FSET);


/* static variables */
FSET emptyset;


void
finit (void)
{
  memset (emptyset, 0, sizeof(FSET));
}


void
funion (register FSET s1, register FSET s2, register FSET s3)
{
  register unsigned int *x, *y, *z;
  FSET tmp;

  z = (unsigned int *) tmp;
  for (x = (unsigned int *) s1; *x; x++)
    {
      for (y = (unsigned int *) s2; *y; y++)
	if ((*x & MASK) == (*y & MASK))
	  break;
      
      if (!*y)
	*z++ = (*x & MASK) | (255 << 16);
    }
  
  for (x = (unsigned int *) s2; *x; x++)
    {
      if (z == (unsigned int *) &tmp[LENGTH-1])
	{
	  fprintf (stderr, "error: overflow in funion\n");
	  fprintf (stderr, "       recompile fset library with a higher LENGHT\n");
	  exit (-1);
	}
      *z++ = *x;
    }
  
  while (z < (unsigned int *) &tmp[LENGTH])
    *z++ = 0;
  fcopy(s3, tmp);
}


void
finter (register FSET s1, register FSET s2, register FSET s3)
{
  register unsigned int *x, *y, *z;
  FSET tmp;
  
  z = (unsigned int *) tmp;
  for (x = (unsigned int *) s1; *x; x++)
    for (y = (unsigned int *) s2; *y; y++)
      if ((*x & MASK) == (*y & MASK))
	{
	  *z++ = *x;
	  break;
	}
  
  while (z < (unsigned int *) &tmp[LENGTH])
    *z++ = 0;
  fcopy(s3, tmp);
}


void
fins (register unsigned short e, register FSET s1, register FSET s2)
{
  register unsigned int *x, *y, found = 0;
  FSET tmp;
    
  y = (unsigned int *) tmp;
  for (x = (unsigned int *) s1; *x; x++)
    {
      if ((*x & MASK) == (e & MASK))
	found = 1;
      *y++ = *x;
    }
  
    if (y == (unsigned int *) &tmp[LENGTH-1])
    {
      fprintf (stderr, "error: overflow in fins\n");
      fprintf (stderr, "       recompile fset library with a higher LENGHT\n");
      exit (-1);
    }
  
  if (!found)
    *y++ = (e | (255 << 16));

  while (y < &tmp[LENGTH])
    *y++ = 0;
  fcopy(s2, tmp);
}


void
fdel (register unsigned int e, register FSET s1, register FSET s2)
{
  register unsigned int *x, *y;
  FSET tmp;
  
  y = (unsigned int *) tmp;
  for (x = (unsigned int *) s1; *x; x++)
    if ((*x & MASK) != (e & MASK))
      *y++ = *x;
  
  while (y < (unsigned int *) &tmp[LENGTH])
    *y++ = 0;
  fcopy(s2, tmp);
}


int
fcmp (register FSET s1, register FSET s2)
{
  register unsigned int *x, *y;

  for (x = (unsigned int *) s1; *x; x++)
    {
      for (y = (unsigned int *) s2; *y; y++)
	if ((*x & MASK)  == (*y & MASK))
	  break;
      
      if (*y)
	return 1;
    }

  for (y = (unsigned int *) s2; *y; y++)
    {
      for (x = (unsigned int *) s1; *x; x++)
	if ((*y & MASK) == (*x & MASK))
	  break;
      
      if (*x)
	return 1;
    }

  return 0;
}


int
fcomm (register FSET s1, register FSET s2)
{
  register unsigned int *x, *y;
  
  for (x = (unsigned int *) s1; *x; x++)
    for (y = (unsigned int *) s2; *y; y++)
      if ((*x & MASK) == (*y & MASK))
	return 1;
  return 0;
}


void 
fucost (register unsigned short cost, register FSET s1, register FSET s2)
{
  register unsigned int *x, *y;
  
  for (x = (unsigned int *) s1; *x; x++)
    for (y = (unsigned int *) s2; *y; y++)
      if (((*x & MASK) == (*y & MASK)) && ((*y >> 16) > cost))
	{
	  *y = (*y & MASK) | (cost << 16);
	  break;
	}
}


short 
fcost (register FSET s1, register FSET s2)
{
  register unsigned int *x, *y, cost = 9999;
  
  for (x = (unsigned int *) s1; *x; x++)
    for (y = (unsigned int *) s2; *y; y++)
      if ((*x & MASK) == (*y & MASK))
        cost = (*y >> 16) < cost ? (*y >> 16) : cost;
  return cost;
}


short 
focost (register FSET s1, register FSET s2)
{
  register unsigned int *x, *y, min = 9999;
  
  for (x = (unsigned int *) s1; *x; x++)
    for (y = (unsigned int *) s2; *y; y++)
      if ((*x & MASK) != (*y & MASK))
	min = ((short) (*y >> 16)) < min ? ((short) (*y >> 16)) : min;
  return min;
}


int   
feother (register unsigned int e, register FSET s)
{
  register unsigned int *x;
  
  for (x = (unsigned int *) s; *x; x++)
    if ((*x & MASK) != (e & MASK))
      return 1;
  return 0;
}


short 
ffirst  (register FSET s)
{
  if (*((unsigned int *) s))
    return (*((unsigned int *) s) & MASK);
}


void
fout (register FILE *stream, register FSET s1)
{
  register unsigned int *x;
  
  fprintf (stream, "{ ");
  for (x = (unsigned int *) s1; *x; x++)
    fprintf (stream, "%u ", *x);
  fprintf (stream, "}");
}
