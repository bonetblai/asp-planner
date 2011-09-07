%{
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>


struct idlist_s {
  char *name;
  struct idlist_s *next;
} idlist_s;

struct domain_s {
  char *name;
  struct idlist_s *vals;
  struct domain_s *next;
} domain_s;

struct predicate_s {
  char *name;
  struct idlist_s *vars;
  struct predicate_s *next;
} predicate_s;

struct instant_s {
  char *var, *val;
  struct instant_s *next;
} instant_s;

struct hashentry_s {
  char *name;
  int  number;
  struct hashentry_s *next;
} hashentry_s;


typedef struct domain_s *domain_p;
typedef struct idlist_s *idlist_p;
typedef struct predicate_s *predicate_p;
typedef struct instant_s *instant_p;
typedef struct hashentry_s *hashentry_p;
typedef union {
  char *      ident;
  idlist_p    idlist;
  predicate_p predicate;
} YYSTYPE_T;

#define YYSTYPE  YYSTYPE_T
#define HASHSIZE 20*1024


/* prototypes */
int yyerror (char *);
int yylex (void);
static int samevar (char *, char *);
static void instantiate_rule (predicate_p, idlist_p, predicate_p, predicate_p,
                              predicate_p, instant_p);
static void instantiate_values (idlist_p, instant_p, void (*)(instant_p));
static void instantiate_predicates (void);
static void emit_prologue (void);
static void emit_epilogue (void);


/* global static variables */
static domain_p    tmp_domain, domains = NULL;
static predicate_p predicates = NULL, global_predicate, tpred;
static int         in_predicates = 1, opname = 1;
static predicate_p global_action, global_prec, global_add, global_del;
static predicate_p initial_situation = NULL, goal_situation = NULL;
static hashentry_p hashtable[HASHSIZE];
static FILE        *xfile, *yfile, *zfile;

static int         lineno = 1;
static char        *file;
%}


%token   PREDICATES OPERATOR VARS PRECONDS
%token   ADDLIST DELLIST IDENT ERROR
%token   RANGES INITIAL GOAL

%type    <ident>  IDENT var
%type    <idlist> ident_list var_list
%type    <predicate> rec_predicates fact_list
%type    <predicate> predicate fact

%start   start


%%


start             :  predicates
                       {  instantiate_predicates ();
		          emit_prologue ();
                       }
                     operators
                       {  emit_epilogue ();  }
                  |  vars_range initial goal
                  ;


predicates        :  '(' PREDICATES rec_predicates
                       {  in_predicates = 0; }              
                     ')'
                  ;


operators         :  operators operator
                  |  /* empty */
                  ;
 

rec_predicates    :  rec_predicates predicate
                       {  $$ = $2;
			  $$->next = $1;
		       }
			  
                  |  /* empty */
                       {  $$ = NULL; }
                  ;


predicate         :  '(' IDENT var_list ')'
                       {  $$ = (predicate_p)
			    malloc (sizeof(struct predicate_s));
		          $$->name = $2;
			  $$->vars = $3;
			  $$->next = NULL;
			  if (in_predicates)
			    {     
			      $$->next = predicates;
			      predicates = $$;
			    }
		       }
                  ;


operator          :  '(' OPERATOR
                           IDENT
                           '(' VARS var_list ')'
                           '(' PRECONDS rec_predicates ')'
                           '(' ADDLIST rec_predicates ')'
                           '(' DELLIST rec_predicates ')'
                     ')'
                       {  tpred = (predicate_p)
			    malloc (sizeof(struct predicate_s));
		          tpred->name = $3;
			  tpred->vars = $6;
			  tpred->next = NULL;
			  instantiate_rule (tpred, $6, $10, $14, $18, NULL);
		       }
                  ;


var_list          :  var var_list
                       {  $$ = (idlist_p)
			    malloc (sizeof(struct idlist_s));
                          $$->name = $1;
                          $$->next = $2;
		       }
                  |  /* empty */
                       {  $$ = NULL; }
                  ;


var               :  '<' IDENT '>'
                       {  $$ = $2;  }
                  ;


vars_range        :  '(' RANGES rec_vars_range ')'
                  ;


rec_vars_range    :  rec_vars_range var_range
                  |  /* empty */
                  ;


var_range         :  '(' IDENT ident_list ')'
                       {  tmp_domain = (domain_p)
			    malloc (sizeof(struct domain_s));
		          tmp_domain->name = $2;
			  tmp_domain->vals = $3;
			  tmp_domain->next = domains;
			  domains = tmp_domain;
		       }
                  ;


initial           :  '(' INITIAL fact_list ')'
                       {  initial_situation = $3;  }
                  ;


goal              :  '(' GOAL fact_list ')'
                       {  goal_situation = $3;  }
                  ;


fact_list         :  fact_list fact
                       {  $$ = $2;
			  $$->next = $1;
		       }
                  |  /* empty */
                       {  $$ = NULL; }
                  ;


fact              :  '(' IDENT ident_list ')'
                       {  $$ = (predicate_p)
			    malloc (sizeof(struct predicate_s));
		          $$->name = $2;
			  $$->vars = $3;
			  $$->next = NULL;
		       }
                  ;


ident_list        :  IDENT ident_list
                       {  $$ = (idlist_p)
			    malloc (sizeof(struct idlist_s));
                          $$->name = $1;
                          $$->next = $2;
		       }
                  |  /* empty */
                       {  $$ = NULL; }
                  ;


%%


int
yyerror (char *s)
{
  fprintf (stderr, "%s: %s(%d)\n", s, file, lineno);
  return 0;
}


int
main (int argc, char **argv)
{
  int fd;
  char buf[1024];

  if (argc != 4)
    {
      fprintf (stderr, "usage: %s <prefix> <fact-file> <op-file>\n", *argv);
      exit (-1);
    }

  sprintf (buf, "%s1.c", *++argv);
  xfile = fopen (buf, "w+");
  sprintf (buf, "%s2.c", *argv);
  yfile = fopen (buf, "w+");
  sprintf (buf, "%s3.c", *argv);
  zfile = fopen (buf, "w+");
  if (!xfile || !yfile || !zfile)
    {
      perror ("main: ");
      exit (-1);
    }

  if ((fd = open (*++argv, O_RDONLY)) == -1)
    {
      perror ("main: ");
      exit (-1);
    }
  else
    {
      /* redirection of fd to stdin */
      close (fileno(stdin));
      dup (fd);
      file = *argv;
      if (yyparse ())
	exit (-1);
      close (fileno(stdin));
      close (fd);
    }
  
  if ((fd = open (*++argv, O_RDONLY)) == -1)
    {
      perror ("main: ");
      exit (-1);
    }
  else
    {
      /* reading of fact file */
      clearerr (stdin);
      dup (fd);
      file = *argv;
      lineno = 1;
      if (yyparse ())
	exit (-1);
      close (fileno(stdin));
      close (fd);
    }

  return 0;
}


int
yylex (void)
{
  int c;
  char *ptr, buf[512];

  ptr = buf;
  *ptr = '\0';

  do {
    if ((c = getchar()) == '\n')
      lineno++;
  } while (isspace(c));

  if (isalpha(c))
    {
      do {
	*ptr++ = toupper(c);
	c = getchar();
      } while (isalpha(c));
      
      if (isdigit(c))
	do {
	  *ptr++ = c;
	  c = getchar();
	} while (isdigit(c));
	  
      if (!isspace(c) && c != ')' && c != '>')
	return ERROR; 
      else
	{
	  ungetc (c, stdin);
	  *ptr = '\0';
	  yylval.ident = strdup (buf);

	  if (!strcmp (buf, "PREDICATES"))
	    return PREDICATES;
	  else if (!strcmp (buf, "OPERATOR"))
	    return OPERATOR;
	  else if (!strcmp (buf, "VARS"))
	    return VARS;
	  else if (!strcmp (buf, "PRECONDS"))
	    return PRECONDS;
	  else if (!strcmp (buf, "ADD"))
	    return ADDLIST;
	  else if (!strcmp (buf, "DEL"))
	    return DELLIST;
	  else if (!strcmp (buf, "RANGES"))
	    return RANGES;
	  else if (!strcmp (buf, "INITIAL"))
	    return INITIAL;
	  else if (!strcmp (buf, "GOAL"))
	    return GOAL;
	  else
	    return IDENT;
	}
    }
  else if (c == EOF)
    return 0;
  else
    return c;
}


static hashentry_p
read_hash (char *key)
{
  unsigned    i;
  char        *p = key;
  hashentry_p e;

  for (i = 0; *p != '\0'; i += (unsigned) *p++); 
  i = i % HASHSIZE;

  for (e = hashtable[i]; e != NULL; e = e->next)
    if (!strcmp (key, e->name))
      return e;

  return NULL;
}


static void
insert_hash (char *key, hashentry_p entry)
{
  unsigned i;
  char *p = key;

  if (!read_hash (key))
    {
      for (i = 0; *p != '\0'; i += (unsigned) *p++);
      i = i % HASHSIZE;

      entry->next = hashtable[i];
      hashtable[i] = entry;
#ifdef DEBUG
      fprintf (stderr, "\"%s\" inserted with %d\n", key, entry->number);
#endif
    }
}


static void
insert_predicate (instant_p insts)
{
  static int  number = 0;
  static char buf[1024];
  hashentry_p hashe;
  idlist_p    vp;
  instant_p   ip;

  strcpy (buf, global_predicate->name);
  strcat (buf, "(");

  for (vp = global_predicate->vars; vp; vp = vp->next)
    for (ip = insts; ip; ip = ip->next)
      if (!strcmp (ip->var, vp->name))
	{
	  strcat (buf, ip->val);
	  if (vp->next)
	    strcat (buf, ",");
	  break;
	}

  strcat (buf, ")");

  if (!read_hash (buf))
    {
      hashe = (hashentry_p) malloc (sizeof(hashentry_s));
      hashe->name = strdup (buf);
      hashe->number = ++number;
      hashe->next = NULL;
      insert_hash (buf, hashe);
    }
}


static void
instantiate_predicates (void)
{
  predicate_p pred;

  for (pred = predicates; pred; pred = pred->next)
    {
      global_predicate = pred;
      instantiate_values (pred->vars, NULL, insert_predicate);
    }
}


static char *
build_predicate (predicate_p pred, instant_p insts)
{
  static char buf[1024];
  idlist_p    vp;
  instant_p   ip;

  strcpy (buf, pred->name);
  strcat (buf, "(");
  for (vp = pred->vars; vp; vp = vp->next)
    for (ip = insts; ip; ip = ip->next)
      if (!strcmp (ip->var, vp->name))
	{
	  strcat (buf, ip->val);
	  if (vp->next)
	    strcat (buf, ",");
	  break;
	}

  strcat (buf, ")");
  return buf;
}


static void
emit_prologue (void)
{
  fprintf (xfile, "/* automatically generated code -- "
                  "DO NOT EDIT BY HAND! */\n\n");
  fprintf (xfile, "#include <stdio.h>\n");
  fprintf (xfile, "#include <string.h>\n");
  fprintf (xfile, "#include \"fset.h\"\n");
  fprintf (xfile, "#include \"asprelplan.h\"\n\n");
  fprintf (xfile, "#include \"relpro-ope.c\"\n\n\n");
  fprintf (xfile, " int inv = 0;\n");
  fprintf (xfile, "void\n");
  fprintf (xfile, "do_actions (void)\n");
  fprintf (xfile, "{\n");
  fprintf (xfile, "  register int cost;\n");
  fprintf (xfile, "  extern int curtime;\n\n");
  fprintf (xfile, "  FSET del, sup;\n");
  fprintf (xfile, "  clean (curtime);\n");
  
  fprintf (yfile, "/* automatically generated code -- "
                  "DO NOT EDIT BY HAND! */\n\n");
  fprintf (yfile, "#include \"asprelplan.h\"\n");

  fprintf (zfile, "/* automatically generated code -- "
                  "DO NOT EDIT BY HAND! */\n\n");
  fprintf (zfile, "#include \"asprelplan.h\"\n\n");
  fprintf (zfile, "extern void fill_table_aux (void);\n\n");
  fprintf (zfile, "void\n");
  fprintf (zfile, "fill_table (void)\n");
  fprintf (zfile, "{\n");
  fprintf (zfile, "  fill_table_aux ();\n");
}


static void
emit_epilogue (void)
{
  static char buf[1024];
  idlist_p    vp;
  hashentry_p entry;
  int         i;

  fprintf (xfile, "}\n\n");
  fprintf (yfile, "void\n");
  fprintf (yfile, "set_initial_situation (void)\n");
  fprintf (yfile, "{\n");
  
  while (initial_situation)
    {
      strcpy (buf, initial_situation->name);
      strcat (buf, "(");
      for (vp = initial_situation->vars; vp; vp = vp->next)
	{
	  strcat (buf, vp->name);
	  if (vp->next)
	    strcat (buf, ",");
	}
      strcat (buf, ")");
      
      if (!(entry = read_hash (buf)))
	{
	  fprintf (stderr, "emit_epilogue: no hash entry for %s\n", buf);
	  exit (-1);
	}
      fprintf (yfile, "  situation[%d].lit = 1;\n", entry->number);
      initial_situation = initial_situation->next;
    }

  fprintf (xfile, "int\n");
  fprintf (xfile, "have_a_goal (void)\n");
  fprintf (xfile, "{\n");
  fprintf (xfile, "  static int goal[] = { ");

  fprintf (yfile, "}\n\n");
  fprintf (yfile, "int\n");
  fprintf (yfile, "goal_situation (literal_p sit)\n");
  fprintf (yfile, "{\n");
  fprintf (yfile, "  return ");

  while (goal_situation)
    {
      strcpy (buf, goal_situation->name);
      strcat (buf, "(");
      for (vp = goal_situation->vars; vp; vp = vp->next)
	{
	  strcat (buf, vp->name);
	  if (vp->next)
	    strcat (buf, ",");
	}
      strcat (buf, ")");
      
      entry = read_hash (buf);
      fprintf (xfile, "%d /* %s */, ", entry->number, buf);
      fprintf (yfile, "sit[%d].lit", entry->number);
      if (goal_situation->next)
	  fprintf (yfile, " && ");
      goal_situation = goal_situation->next;
    }

  fprintf (xfile, "0 };\n");
  fprintf (xfile, "  register int *ip, cost = 0;\n\n");
  fprintf (xfile, "  inv++;\n");
  fprintf (xfile, "  check_preconds (goal, goal, curtime);\n");
  fprintf (xfile, "  if (next_preconds ())\n");
  fprintf (xfile, "    {\n");
  fprintf (xfile, "      for (ip = goal; *ip; ip++)\n"); 
  fprintf (xfile, "        cost += present[*ip][time[*ip]].cost;\n");
  fprintf (xfile, "      ptime = 0;\n");
  fprintf (xfile, "      return 1 + cost;\n");
  fprintf (xfile, "    }\n");
  fprintf (xfile, "  else\n");
  fprintf (xfile, "    return 0;\n");
  fprintf (xfile, "}\n");

  fprintf (yfile, ";\n");
  fprintf (yfile, "}\n\n");
  fprintf (yfile, "void\n");
  fprintf (yfile, "fill_table_aux (void)\n");
  fprintf (yfile, "{\n");

  for (i = 1; i < opname; i++)
    {
      fprintf (yfile, "  opertable[%d] = operator%d;\n", i, i);
      fprintf (zfile, "  operators[%d].function = opertable[%d];\n", i, i);
    }
  fprintf (yfile, "}\n");
  fprintf (zfile, "\n  numoper = %d;\n", opname);
  fprintf (zfile, "}\n");
}


static void
emit_rule (instant_p insts)
{
  predicate_p p;
  hashentry_p entry;
  int         prec[128], add[128], del[128];
  int         i, *ip, *pp;
  char        *pn;
  

  memset (prec, 0, 128);
  memset (add, 0, 128);
  memset (del, 0, 128);


  /* generating comments */
  fprintf (xfile, "\n\n/* generated code for action %s "
                  "with values:\n", global_action->name);
  fprintf (xfile, "\tpreconds = ");
  fprintf (yfile, "\n\n/* generated code for action %s "
                  "with values:\n", global_action->name);
  fprintf (yfile, "\tpreconds = ");
  for (ip = prec, p = global_prec; p; p = p->next)
    {
      entry = read_hash (pn = build_predicate (p, insts));
      if (!entry)
	{
	  fprintf (stderr, "emit_rule: no hash entry for %s\n", pn);
	  exit (-1);
	}
      *ip++ = entry->number;
      fprintf (xfile, "%s ", pn);
      fprintf (yfile, "%s ", pn);
    }
  fprintf (xfile, "\n\tadd-list = ");
  fprintf (yfile, "\n\tadd-list = ");
  for (ip = add, p = global_add; p; p = p->next)
    {
      entry = read_hash (pn = build_predicate (p, insts));
      if (!entry)
	{
	  fprintf (stderr, "emit_rule: no hash entry for %s\n", pn);
	  exit (-1);
	}
      *ip++ = entry->number;
      fprintf (xfile, "%s ", pn);
      fprintf (yfile, "%s ", pn);
    }
  fprintf (xfile, "\n\tdel-list = ");
  fprintf (yfile, "\n\tdel-list = ");
  for (ip = del, p = global_del; p; p = p->next)
    {
      entry = read_hash (pn = build_predicate (p, insts));
      if (!entry)
	{
	  fprintf (stderr, "emit_rule: no hash entry for %s\n", pn);
	  exit (-1);
	}
      *ip++ = entry->number;
      fprintf (xfile, "%s ", pn);
      fprintf (yfile, "%s ", pn);
    }
  fprintf (xfile, "\n   Operator ID = %d */\n", opname);
  fprintf (yfile, "\n   Operator ID = %d */\n", opname);


  /* generating new function name */
  fprintf (yfile, "int\n");
  fprintf (yfile, "operator%d (void)\n", opname);
  fprintf (yfile, "{\n");
  fprintf (yfile, "  register int tmp = ");
  fprintf (zfile, "  operators[%d].name = \"%s\";\n",
	   opname, build_predicate (global_action, insts));


  /* generating code for tmp variable */
  fprintf (xfile, "  check_preconds (operators[%d].prc, operators[%d].prc, curtime);\n",
	   opname, opname);
  fprintf (xfile, "  if (next_preconds ())\n");
  fprintf (xfile, "    {\n");
  for (i = 0, pp = prec; *pp; i++)
    {
      fprintf (yfile, "situation[%d].lit", *pp);
      fprintf (zfile, "  operators[%d].prc[%d] = %d;\n", opname, i, *pp++);
      if (*pp)
	{
	  fprintf (yfile, " && ");
	}
    }
  fprintf (yfile, ";\n");
  fprintf (zfile, "  operators[%d].prc[%d] = 0;\n", opname, i);
  

  /* generating code for add-list */
  for (i = 0, ip = add; *ip; i++, ip++)
    {
      fprintf (yfile, "  new_situation[%d].lit |= tmp;\n", *ip);
      fprintf (zfile, "  operators[%d].add[%d] = %d;\n", opname, i, *ip);
    }
  fprintf (zfile, "  operators[%d].add[%d] = 0;\n", opname, i);

  fprintf (xfile, "      do {\n");
  fprintf (xfile, "          cost = 1;\n\n");
  fprintf (xfile, "          /* cost */\n");
  for (pp = prec; *pp; pp++)
    fprintf (xfile, "          cost += present[%d][time[%d]].cost;\n", *pp, *pp);
  for (ip = add; *ip; ip++)
    {
      fprintf (xfile, "          if (!present[%d][curtime].prst)\n", *ip);
      fprintf (xfile, "            present[%d][curtime].cost = cost;\n", *ip);
      fprintf (xfile, "          else if (present[%d][curtime].cost > cost)\n", *ip);
      fprintf (xfile, "            present[%d][curtime].cost = cost;\n", *ip);

      fprintf (xfile, "          present[%d][curtime].prst = 1;\n", *ip);
    }

  fprintf (xfile, "      }\n");
  fprintf (xfile, "      while (next_preconds ());\n");
  fprintf (xfile, "    }\n");


  /* generating code for del-list */
  for (i = 0, ip = del; *ip; i++, ip++)
    {
      fprintf (yfile, "  new_situation[%d].lit &= !tmp;\n", *ip);
      fprintf (zfile, "  operators[%d].del[%d] = %d;\n", opname, i, *ip);
    }
  fprintf (zfile, "  operators[%d].del[%d] = 0;\n", opname, i);
  

  /* close function */
  fprintf (yfile, "  return tmp;\n");
  fprintf (yfile, "}\n\n");


  /* increment operator ID */
  opname++;
}


static void
instantiate_rule (predicate_p pred, idlist_p vars, predicate_p precs,
		  predicate_p adds, predicate_p dels, instant_p insts)
{
  global_action = pred;
  global_prec = precs;
  global_add = adds;
  global_del = dels;
  instantiate_values (vars, NULL, emit_rule);
}


/* receive a function that is called each time we find
   a complete instantiation of the vars.   */

static void
instantiate_values (idlist_p var, instant_p insts,
		    void (*func)(instant_p))
{
  domain_p  dom;
  idlist_p  val;
  instant_p tmp, t2;

  if (!var)
    {
      for (tmp = insts; tmp != NULL; tmp = tmp->next)
	for (t2 = insts; t2 != NULL; t2 = t2->next)
	  if (samevar (tmp->var, t2->var) && tmp != t2 &&
	      !strcmp (tmp->val, t2->val))
	    return;
      (*func)(insts);
      return;
    }

  for (dom = domains; dom; dom = dom->next)
    if (samevar (dom->name, var->name))
	{
	  for (val = dom->vals; val; val = val->next)
	    {
	      tmp = (instant_p) malloc (sizeof(instant_s));
	      tmp->var = var->name;
	      tmp->val = val->name;
	      tmp->next = insts;
	      
	      instantiate_values (var->next, tmp, func);
	      
	      free (tmp);
	    }
	  return;
	}
}


static int
samevar (char *var1, char *var2)
{
  while (isalpha(*var1) && isalpha(*var2) && *var1++ == *var2++);
  return !isalpha(*var1) && !isalpha(*var2);
}
