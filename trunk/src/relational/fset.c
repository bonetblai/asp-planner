#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "fset.h"


/* prototypes */
void finit  (void);
void funion (register FSET, register FSET, register FSET);
void finter (register FSET, register FSET, register FSET);
void fins   (register unsigned short, register FSET, register FSET);
void fdel   (register unsigned short, register FSET, register FSET);
int  fcmp   (register FSET, register FSET);
void fout   (register FILE *, register FSET);


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
  register unsigned short *x, *y, *z;
  FSET tmp;

  z = (unsigned short *) tmp;
  for (x = (unsigned short *) s1; *x; x++)
    {
      for (y = (unsigned short *) s2; *y; y++)
	if (*x == *y)
	  break;

      if (*y)
	*z++ = *x;
    }
  
  for (y = (unsigned short *) s2; *y; y++)
    {
      if (z == (unsigned short *) &tmp[LENGTH-1])
	{
	  fprintf (stderr, "error: overflow in funion\n");
	  fprintf (stderr, "       recompile fset library with a higher LENGHT\n");
	  exit (-1);
	}
      *z++ = *x;
    }
  
  while (z < (unsigned short *) &tmp[LENGTH])
    *z++ = 0;
  fcopy(s3, tmp);
}


void
finter (register FSET s1, register FSET s2, register FSET s3)
{
  register unsigned short *x, *y, *z;
  FSET tmp;
  
  z = (unsigned short *) tmp;
  for (x = (unsigned short *) s1; *x; x++)
    for (y = (unsigned short *) s2; *y; y++)
      if (*x == *y)
	{
	  *z++ = *x;
	  break;
	}
  
  while (z < (unsigned short *) &tmp[LENGTH])
    *z++ = 0;
  fcopy(s3, tmp);
}


void
fins (register unsigned short e, register FSET s1, register FSET s2)
{
  register unsigned short *x, *y;
  FSET tmp;
    
  y = (unsigned short *) tmp;
  for (x = (unsigned short *) s1; *x; x++)
    if (*x != e)
      *y++ = *x;
  
  if (y == (unsigned short *) &tmp[LENGTH-1])
    {
      fprintf (stderr, "error: overflow in fins\n");
      fprintf (stderr, "       recompile fset library with a higher LENGHT\n");
      exit (-1);
    }
  
  *y++ = e;
  while (y < &tmp[LENGTH])
    *y++ = 0;
  fcopy(s2, tmp);
}


void
fdel (register unsigned short e, register FSET s1, register FSET s2)
{
  register unsigned short *x, *y;
  FSET tmp;
  
  y = (unsigned short *) tmp;
  for (x = (unsigned short *) s1; *x; x++)
    if (*x != e)
      *y++ = *x;
  
  while (y < (unsigned short *) &tmp[LENGTH])
    *y++ = 0;
  fcopy(s2, tmp);
}


int
fcmp (register FSET s1, register FSET s2)
{
  register unsigned short *x, *y;

  for (x = (unsigned short *) s1; *x; x++)
    {
      for (y = (unsigned short *) s2; *y; y++)
	if (*x == *y)
	  break;
      
      if (*y)
	return 1;
    }

  for (y = (unsigned short *) s2; *y; y++)
    {
      for (x = (unsigned short *) s1; *x; x++)
	if (*y == *x)
	  break;
      
      if (*x)
	return 1;
    }

  return 0;
}


void
fout (register FILE *stream, register FSET s1)
{
  register unsigned short *x;
  
  fprintf (stream, "{ ");
  for (x = (unsigned short *) s1; *x; x++)
    fprintf (stream, "%u ", *x);
  fprintf (stream, "}");
}
