%{
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

#define EQUAL    1
#define NOTEQUAL 2
#define ASSIGN   3 
#define LVALUE   4 
#define RVALUE   5 
#define VARIABLE 6 
#define ROBJECT  7 

struct idlist_s {
  char *name;
  struct idlist_s *next;
} idlist_s;

struct domain_s {
  char *name;
  int num;
  struct idlist_s *vals;
  struct domain_s *next;
} domain_s;

struct fluent_s {
  char *name;
  struct idlist_s *vars;
  struct fluent_s *next;
} fluent_s;

struct operator_s {
  char *name;
  struct idlist_s *vars;
  struct operator_s *next;
} operator_s;

struct object_s {
  char *name;
  struct fluent_s *fluents;
  struct object_s *next;
} object_s;

struct app_s {
  char *fluent;
  struct app_s *next;
} app_s;

struct value_s {
  int type;
  int btype;
  char *basic;
  struct app_s *fluent;
} value_s;

struct cond_s {
  int op;
  struct value_s *lvalue;
  struct value_s *rvalue;
  struct cond_s *next;
} cond_s;

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
typedef struct fluent_s *fluent_p;
typedef struct operator_s *operator_p;
typedef struct object_s *object_p;
typedef struct cond_s *cond_p;
typedef struct instant_s *instant_p;
typedef struct hashentry_s *hashentry_p;
typedef struct app_s *app_p;
typedef struct value_s *value_p;
typedef union {
  char *   ident;
  idlist_p idlist;
  fluent_p fluent;
  object_p object;
  cond_p   cond;
  value_p  value;
} YYSTYPE_T;

#define YYSTYPE  YYSTYPE_T
#define HASHSIZE 20*1024


/* prototypes */
int yyerror (char *);
int yylex (void);
static int samevar (char *, char *);
static void instantiate_operator (operator_p, idlist_p, cond_p, cond_p);
static void instantiate_values (idlist_p, instant_p, void (*)(instant_p));
static void emit_prologue (void);
static void emit_epilogue (void);


/* global static variables */
static domain_p    tmp_domain, domains = NULL;
static int         in_predicates = 1, opname = 1, object;
static operator_p  global_operator, toper;
static cond_p      global_preconds, global_effects;
static idlist_p    global_vars;
static cond_p      initial_situation = NULL, goal_situation = NULL;
static object_p    objects = NULL;
static app_p       ap, tap;
static hashentry_p hashtable[HASHSIZE];
static FILE        *hfile, *xfile, *yfile, *zfile;

static int         lineno = 1;
static char        *file, *hfilename;
%}


%token   PREDICATES OPERATOR VARS PRECONDS
%token   OBJECT EFFECTS IDENT ERROR
%token   INSTANTIATION INITIAL GOAL

%type    <ident>  IDENT var
%type    <idlist> ident_list var_list
%type    <fluent> rec_fluents fluent
%type    <object> objects object
%type    <cond>   condition conditions effect effects fact_list
%type    <value>  lvalue rvalue basic_value

%start   start


%%


start             :  objects '$' '$' operators {}
                  |  instantiations initial goal
                  ;


objects           :  object objects
                       {
			 objects = $1;
			 objects->next = $2;
		       }
                  |  /* empty */
		       { $$ = NULL; }
                  ;

object            :  '(' OBJECT IDENT rec_fluents ')'
                       { 
			 if (!($$ = (object_p) malloc (sizeof(struct object_s))))
			   {
			     fprintf (stderr, "not enough memory.\n");
			     exit (-1);
			   } 
			 $$->name = $3;
			 $$->fluents = $4;
			 $$->next = NULL;
		       }
                  ;


operators         :  operator operators 
                  |  /* empty */
                  ;
 

rec_fluents       :  rec_fluents fluent
                       {
			 $$ = $2;
			 $$->next = $1;
		       }
                  |  /* empty */
                       { $$ = NULL; }
                  ;


fluent            :  '(' IDENT '(' var_list ')' ')'
                       {
			 if (!($$ = (fluent_p) malloc (sizeof(struct fluent_s))))
			   {
			     fprintf (stderr, "not enough memory.\n");
			     exit (-1);
			   }
			 $$->name = $2;
			 $$->vars = $4;
			 $$->next = NULL;
		       }
                  ;


operator          :  '(' OPERATOR IDENT
                           '(' VARS var_list ')'
                           '(' PRECONDS conditions ')'
                           '(' EFFECTS effects ')'
                     ')'
                       {
			 if (!(toper = (operator_p) malloc (sizeof(struct operator_s))))
			   {
			     fprintf (stderr, "not enough memory.\n");
			     exit (-1);
			   }
			 toper->name = $3;
			 toper->vars = $6;
			 toper->next = NULL;
			 instantiate_operator (toper, $6, $10, $14);
		       }
                  ;


var_list          :  var var_list
                       {
			 if (!($$ = (idlist_p) malloc (sizeof(struct idlist_s))))
			   {
			     fprintf (stderr, "not enough memory.\n");
			     exit (-1);
			   }
			 $$->name = $1;
			 $$->next = $2;
		       }
                  |  /* empty */
                       { $$ = NULL; }
                  ;


var               :  '<' IDENT '>'
                       { $$ = $2; }
                  ;


conditions        :  conditions condition
                       {
			 $2->next = $1;
			 $$ = $2;
		       }
                  |  /* empty */
                       { $$ = NULL; }
                  ;


effects           :  effect effects
                       {
			 $1->next = $2;
			 $$ = $1;
		       }
                  |  /* empty */
                       { $$ = NULL; }
                  ;


condition         :  '(' rvalue '=' '=' rvalue ')'
                       {
			 if (!($$ = (cond_p) malloc (sizeof(struct cond_s))))
			   {
			     fprintf (stderr, "not enough memory.\n");
			     exit (-1);
			   }
			 $$->lvalue = $2;
			 $$->rvalue = $5;
			 $$->op = EQUAL;
		       }
                  |  '(' rvalue '!' '=' rvalue ')'
                       {
			 if (!($$ = (cond_p) malloc (sizeof(struct cond_s))))
			   {
			     fprintf (stderr, "not enough memory.\n");
			     exit (-1);
			   }
			 $$->lvalue = $2;
			 $$->rvalue = $5;
			 $$->op = NOTEQUAL;
		       }
                  ;


effect            :  '(' lvalue '=' rvalue ')'
                       {
			 if (!($$ = (cond_p) malloc (sizeof(struct cond_s))))
			   {
			     fprintf (stderr, "not enough memory.\n");
			     exit (-1);
			   }
			 $$->lvalue = $2;
			 $$->rvalue = $4;
			 $$->op = ASSIGN;
		       }
                  ;


lvalue            :  lvalue '.' IDENT
                       {
			 if (!(tap = (app_p) malloc (sizeof(struct app_s))))
			   {
			     fprintf (stderr, "not enough memory.\n");
			     exit (-1);
			   }
			 tap->fluent = $3;
			 tap->next = NULL;
			 for (ap = $1->fluent; ap->next; ap = ap->next);
			 ap->next = tap;
			 $$ = $1;
		       }
                  |  basic_value '.' IDENT
                       {
			 $$ = $1;
			 $$->type = LVALUE;
			 if (!($$->fluent = (app_p) malloc (sizeof(struct app_s))))
			   {
			     fprintf (stderr, "not enough memory.\n");
			     exit (-1);
			   }
			 $$->fluent->fluent = $3;
			 $$->fluent->next = NULL;
		       }
                  ;


rvalue            :  rvalue '.' IDENT
                       {
			 if (!(tap = (app_p) malloc (sizeof(struct app_s))))
			   {
			     fprintf (stderr, "not enough memory.\n");
			     exit (-1);
			   }
			 tap->fluent = $3;
			 tap->next = NULL;
			 for (ap = $1->fluent; ap && ap->next; ap = ap->next);
			 if (ap)
			   ap->next = tap;
			 else
			   $1->fluent = tap;
			 $$ = $1;
		       }
                  |  basic_value
                       {
			 $$ = $1;
			 $$->type = RVALUE;
		       }
                  ;


basic_value       :  IDENT
                       {
			 if (!($$ = (value_p) malloc (sizeof(struct value_s))))
			   {
			     fprintf (stderr, "not enough memory.\n");
			     exit (-1);
			   }
			 $$->basic = $1;
			 $$->btype = ROBJECT;
		       }
                  |  '<' IDENT '>'
                       {
			 if (!($$ = (value_p) malloc (sizeof(struct value_s))))
			   {
			     fprintf (stderr, "not enough memory.\n");
			     exit (-1);
			   }
			 $$->basic = $2;
			 $$->btype = VARIABLE;
		       }
                  ;


instantiations    :  '(' INSTANTIATION rec_instantiation ')'
                  ;


rec_instantiation :  rec_instantiation instantiation
                  |  /* empty */
                  ;


instantiation     :  '(' IDENT ident_list ')'
                       {
			 if (!(tmp_domain = (domain_p) malloc (sizeof(struct domain_s))))
			   {
			     fprintf (stderr, "not enough memory.\n");
			     exit (-1);
			   }
			 tmp_domain->name = $2;
			 tmp_domain->vals = $3;
			 tmp_domain->next = domains;
			 domains = tmp_domain;

			 object = 1;
			 while ($3)
			   {
			     if (!strcmp ($3->name, $2))
			       {
				 yyerror ("cannot instantiate an object with name equal to some class.\n");
				 exit (-1);
			       }
			     fprintf (hfile, "#define %s\t\t(%d)\n", $3->name, object++);
			     $3 = $3->next;
			   }
			 fprintf (hfile, "\n");
			 tmp_domain->num = object;
		       }
                  ;


initial           :  '(' INITIAL fact_list ')'
                       { initial_situation = $3; }
                  ;


goal              :  '(' GOAL fact_list ')'
                       { goal_situation = $3; }
                  ;


fact_list         :  fact_list effect
                       {
			 if ($2->lvalue->btype == VARIABLE)
			   {
			     yyerror ("cannot use a variable here");
			     exit (-1);
			   }
			 $$ = $2;
			 $$->next = $1;
		       }
                  |  /* empty */
                       { $$ = NULL; }
                  ;


ident_list        :  IDENT ident_list
                       {
			 if (!($$ = (idlist_p) malloc (sizeof(struct idlist_s))))
			   {
			     fprintf (stderr, "not enough memory.\n");
			     exit (-1);
			   }
			 $$->name = $1;
			 $$->next = $2;
		       }
                  |  /* empty */
                       { $$ = NULL; }
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

  sprintf (buf, "%s.h", *++argv);
  hfilename = strdup (buf);
  hfile = fopen (buf, "w+");
  sprintf (buf, "%s1.c", *argv);
  xfile = fopen (buf, "w+");
  sprintf (buf, "%s2.c", *argv);
  yfile = fopen (buf, "w+");
  sprintf (buf, "%s3.c", *argv);
  zfile = fopen (buf, "w+");
  if (!hfile || !xfile || !yfile || !zfile)
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
      emit_prologue ();

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

      emit_epilogue ();
    }

  fclose (hfile);
  fclose (xfile);
  fclose (yfile);
  fclose (zfile);
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
      } while (isalpha(c) || (c == '_'));
      
      if (isdigit(c))
	do {
	  *ptr++ = c;
	  c = getchar();
	} while (isdigit(c));
	  
      if (!isspace(c) && c != ')' && c != '>' && c != '.')
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
	  else if (!strcmp (buf, "OBJECT"))
	    return OBJECT;
	  else if (!strcmp (buf, "EFFECTS"))
	    return EFFECTS;
	  else if (!strcmp (buf, "INSTANTIATION"))
	    return INSTANTIATION;
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


static char *
lvalue (value_p lval, app_p fluents, instant_p insts, char *state)
{
  char *op;
  object_p obj;
  fluent_p flp;
  static char buf[1024];
  static char tmp[1024];

  if (lval)
    {
      if (lval->btype == VARIABLE)
	{
	  for (; insts; insts = insts->next)
	    if (!strcmp (insts->var, lval->basic))
	      {
		op = insts->val;
		break;
	      }
	}
      else
	op = lval->basic;

      sprintf (buf, "%s", op);
      return lvalue (NULL, lval->fluent, insts, state);
    }
  else if (fluents)
    {
      for (obj = objects; obj; obj = obj->next)
	for (flp = obj->fluents; flp; flp = flp->next)
	  if (!strcmp (fluents->fluent, flp->name))
	    goto get_it;

      fprintf (stderr, "fluent %s not found in object definitions.\n", fluents->fluent);
      exit (-1);
    get_it:
      if (fluents->next)
	sprintf (tmp, "LVAL(%s, %s, %s, %s) & 0xFF", state, obj->name, buf, fluents->fluent);
      else
	sprintf (tmp, "LVAL(%s, %s, %s, %s)", state, obj->name, buf, fluents->fluent);
      strcpy (buf, tmp);
      return lvalue (NULL, fluents->next, insts, state);
    }
  else
    return buf;
}


static char *
rvalue (value_p rval, app_p fluents, instant_p insts, char *state)
{
  char *lval, *op;
  domain_p dp;
  idlist_p ip;
  static char buf[1024];

  if (rval && !rval->fluent)
    {
      if (rval->btype == VARIABLE)
	{
	  for (; insts; insts = insts->next)
	    if (!strcmp (insts->var, rval->basic))
	      {
		op = insts->val;
		break;
	      }
	}
      else
	op = rval->basic;

      for (dp = domains; dp; dp = dp->next)
	for (ip = dp->vals; ip; ip = ip->next)
	  if (!strcmp (ip->name, op))
	    goto found;
      
      fprintf (stderr, "object %s not found in instantiations.\n", op);
      exit (-1);
    found:
      sprintf (buf, "SVAL(%s, %s, %s)->REF", state, dp->name, op);
      return buf;
    }
  else
    {
      lval = lvalue (rval, fluents, insts, state);
      sprintf (buf, "%s->REF", lval);
      return lval;
    }
}


static char *
hlvalue (value_p lval, app_p fluents, instant_p insts, char *state)
{
  char *op;
  object_p obj;
  fluent_p flp;
  static int flag = 1;
  static char buf[1024];
  static char tmp[1024];

  if (lval)
    {
      if (lval->btype == VARIABLE)
	{
	  for (; insts; insts = insts->next)
	    if (!strcmp (insts->var, lval->basic))
	      {
		op = insts->val;
		break;
	      }
	}
      else
	op = lval->basic;

      sprintf (buf, "%s", op);
      return hlvalue (NULL, lval->fluent, insts, state);
    }
  else if (fluents)
    {
      for (obj = objects; obj; obj = obj->next)
	for (flp = obj->fluents; flp; flp = flp->next)
	  if (!strcmp (fluents->fluent, flp->name))
	    goto get_it;

      fprintf (stderr, "fluent %s not found in object definitions.\n", fluents->fluent);
      exit (-1);
    get_it:
      if (flag)
	{
	  sprintf (tmp, "LVAL(%s, %s, %s, %s)", state, obj->name, buf, fluents->fluent);
	  flag = 0;
	}
      else
	sprintf (tmp, "HVAL(%s, %s, %s, %s)", state, obj->name, buf, fluents->fluent);
      strcpy (buf, tmp);
      return hlvalue (NULL, fluents->next, insts, state);
    }
  else
    {
      flag = 1;
      return buf;
    }
}


static void
emit_prologue (void)
{
  fprintf (hfile, "/* automatically generated code -- DO NOT EDIT BY HAND! */\n\n");
  fprintf (hfile, "#include \"fset.h\"\n\n");
  fprintf (hfile, "#define SVAL(state, obj, idx)\t\t(&(state->obj[idx]))\n");
  fprintf (hfile, "#define LVAL(state, obj, idx, fluent)\t((&(state->obj[idx]))->fluent)\n");
  fprintf (hfile, "#define HVAL(state, obj, idx, fluent)\t((&(state->obj[(ffirst (idx)) & 0xFF]))->fluent)\n\n");

  fprintf (xfile, "/* automatically generated code -- DO NOT EDIT BY HAND! */\n\n");
  fprintf (xfile, "#include <stdio.h>\n");
  fprintf (xfile, "#include <string.h>\n");
  fprintf (xfile, "#include <aspfunplan.h>\n");
  fprintf (xfile, "#define IMPORT\textern\n");
  fprintf (xfile, "#include \"%s\"\n\n", hfilename);
  fprintf (xfile, "void\n");
  fprintf (xfile, "do_actions (void)\n");
  fprintf (xfile, "{\n");
  fprintf (xfile, "  register int cost, tmp;\n");
  fprintf (xfile, "  extern int curtime;\n");
  fprintf (xfile, "  memcpy (&META_N_STATE, &META_I_STATE, sizeof(struct META_STATE_s));\n\n");
    
  fprintf (yfile, "/* automatically generated code -- DO NOT EDIT BY HAND! */\n\n");
  fprintf (yfile, "#include <aspfunplan.h>\n");
  fprintf (yfile, "#define IMPORT\n");
  fprintf (yfile, "#include \"%s\"\n", hfilename);

  fprintf (zfile, "/* automatically generated code -- DO NOT EDIT BY HAND! */\n\n");
  fprintf (zfile, "#include <stdlib.h>\n");
  fprintf (zfile, "#include <aspfunplan.h>\n");
  fprintf (zfile, "#define IMPORT\textern\n");
  fprintf (zfile, "#include \"%s\"\n\n", hfilename);
  fprintf (zfile, "extern void fill_table_aux (void);\n\n");
  fprintf (zfile, "void\n");
  fprintf (zfile, "fill_table (void)\n");
  fprintf (zfile, "{\n");
  fprintf (zfile, "  int i;\n\n");
  fprintf (zfile, "  fill_table_aux ();\n\n");
}


static void
emit_epilogue (void)
{
  int         i, j;
  cond_p      cp;
  object_p    obj;
  fluent_p    flp;
  app_p       ap;
  domain_p    dp;
  idlist_p    ip;

  fprintf (xfile, "\n  memcpy (&META_I_STATE, &META_N_STATE, sizeof(struct META_STATE_s));\n");
  fprintf (xfile, "}\n\n");

  fprintf (xfile, "void\n");
  fprintf (xfile, "start (register STATE_p sit)\n");
  fprintf (xfile, "{\n");
  fprintf (xfile, "  memset (&META_I_STATE, 0, sizeof(struct META_STATE_s));\n");
  for (dp = domains; dp; dp = dp->next)
    for (ip = dp->vals; ip; ip = ip->next)
      {
	fprintf (xfile, "  fins (sit->%s[%s].REF, META_I_STATE.%s[%s].REF, META_I_STATE.%s[%s].REF);\n",
		 dp->name, ip->name, dp->name, ip->name, dp->name, ip->name);
	fprintf (xfile, "  fucost (0, META_I_STATE.%s[%s].REF, META_I_STATE.%s[%s].REF);\n",
		 dp->name, ip->name, dp->name, ip->name);
	for (obj = objects; obj; obj = obj->next)
	  if (!strcmp (obj->name, dp->name))
	    for (flp = obj->fluents; flp; flp = flp->next)
	      {
		fprintf (xfile, "  fins (sit->%s[%s].%s, META_I_STATE.%s[%s].%s, META_I_STATE.%s[%s].%s);\n",
			 obj->name, ip->name, flp->name, obj->name, ip->name, flp->name, obj->name, ip->name, flp->name);
		fprintf (xfile, "  fucost (0, META_I_STATE.%s[%s].%s, META_I_STATE.%s[%s].%s);\n",
			 obj->name, ip->name, flp->name, obj->name, ip->name, flp->name);
	      }
      }
  fprintf (xfile, "}\n\n");

  fprintf (yfile, "void\n");
  fprintf (yfile, "set_initial_situation (void)\n");
  fprintf (yfile, "{\n");
  for (i = 1, dp = domains; dp; dp = dp->next, i++)
    for (j = 1, ip = dp->vals; ip; ip = ip->next, j++)
      fprintf (yfile, "  I_STATE.%s[%d].REF = %d;\n", dp->name, j, ((i << 8) | j));
  fprintf (yfile, "\n");
  for (cp = initial_situation; cp; cp = cp->next)
    {
      fprintf (yfile, "  %s ", lvalue (cp->lvalue, NULL, NULL, "(&I_STATE)"));
      fprintf (yfile, "= %s;\n", rvalue (cp->rvalue, NULL, NULL, "(&I_STATE)"));
    }
  fprintf (yfile, "}\n\n");

  fprintf (yfile, "int\n");
  fprintf (yfile, "goal_situation (STATE_p state)\n");
  fprintf (yfile, "{\n");
  fprintf (yfile, "  return ");
  for (cp = goal_situation; cp; cp = cp->next)
    {
      fprintf (yfile, "(%s ", lvalue (cp->lvalue, NULL, NULL, "state"));
      fprintf (yfile, "== %s)", rvalue (cp->rvalue, NULL, NULL, "state"));
      if (cp->next)
	fprintf (yfile, " && ");
    }
  fprintf (yfile, ";\n");
  fprintf (yfile, "}\n\n");

  fprintf (yfile, "void\n");
  fprintf (yfile, "print_state (void)\n");
  fprintf (yfile, "{\n");
  fprintf (yfile, "}\n\n");

  fprintf (xfile, "int\n");
  fprintf (xfile, "have_a_goal (void)\n");
  fprintf (xfile, "{\n");
  fprintf (xfile, "  register int cost = 0, tmp = ");
  for (cp = goal_situation; cp; cp = cp->next)
    {
      fprintf (xfile, "(fcomm (%s, ", rvalue (cp->rvalue, NULL, NULL, "(&META_I_STATE)"));
      fprintf (xfile, "%s))", hlvalue (cp->lvalue, NULL, NULL, "(&META_I_STATE)"));
      if (cp->next)
	fprintf (xfile, " && ");
      else
	fprintf (xfile, ";\n\n");
    }
  fprintf (xfile, "  if (tmp)\n");
  fprintf (xfile, "    {\n");
  fprintf (xfile, "      cost = 1;\n");
  for (cp = goal_situation; cp; cp = cp->next)
    {
      fprintf (xfile, "      cost += fcost (%s, ", rvalue (cp->rvalue, NULL, NULL, "(&META_I_STATE)"));
      fprintf (xfile, "%s);\n", hlvalue (cp->lvalue, NULL, NULL, "(&META_I_STATE)"));
    }
  fprintf (xfile, "    }\n");
  fprintf (xfile, "  return cost;\n");
  fprintf (xfile, "}\n");
  
  fprintf (yfile, "void\n");
  fprintf (yfile, "fill_table_aux (void)\n");
  fprintf (yfile, "{\n");
  fprintf (zfile, "\n  for (i = 1; i < %d; i++)\n", opname);
  fprintf (zfile, "    operators[i].function = opertable[i];\n");
  fprintf (zfile, "  numoper = %d;\n", opname);
  fprintf (zfile, "}\n");
  for (i = 1; i < opname; i++)
    fprintf (yfile, "  opertable[%d] = operator%d;\n", i, i);
  fprintf (yfile, "}\n");
  

  /* generate objects */
  for (dp = domains; dp; dp = dp->next)
    {
      fprintf (hfile, "struct %s_s {\n", dp->name);
      fprintf (hfile, "  int REF;\n");
      for (obj = objects; obj; obj = obj->next)
	if (!strcmp (obj->name, dp->name))
	  break;
      if (obj)
	{
	  for (flp = obj->fluents; flp; flp = flp->next)
	    fprintf (hfile, "  int %s;\n", flp->name);
	}
      fprintf (hfile, "} %s_s;\n", dp->name);
      fprintf (hfile, "typedef struct %s_s *%s_p;\n\n", dp->name, dp->name);
    }
  fprintf (hfile, "struct STATE_s {\n");
  for (dp = domains; dp; dp = dp->next)
    fprintf (hfile, "  struct %s_s %s[%d];\n", dp->name, dp->name, dp->num);
  fprintf (hfile, "} STATE_s;\n");
  fprintf (hfile, "typedef struct STATE_s *STATE_p;\n\n");
  fprintf (hfile, "IMPORT struct STATE_s I_STATE, N_STATE;\n\n");

  /* generate meta-objects */
  for (dp = domains; dp; dp = dp->next)
    {
      fprintf (hfile, "struct META_%s_s {\n", dp->name);
      fprintf (hfile, "  FSET REF;\n");
      for (obj = objects; obj; obj = obj->next)
	if (!strcmp (obj->name, dp->name))
	  break;
      if (obj)
	{
	  for (flp = obj->fluents; flp; flp = flp->next)
	    fprintf (hfile, "  FSET %s;\n", flp->name);
	}
      fprintf (hfile, "} META_%s_s;\n", dp->name);
      fprintf (hfile, "typedef struct META_%s_s *META_%s_p;\n\n", dp->name, dp->name);
    }
  fprintf (hfile, "struct META_STATE_s {\n");
  for (dp = domains; dp; dp = dp->next)
    fprintf (hfile, "  struct META_%s_s %s[%d];\n", dp->name, dp->name, dp->num);
  fprintf (hfile, "} META_STATE_s;\n");
  fprintf (hfile, "typedef struct META_STATE_s *META_STATE_p;\n\n");
  fprintf (hfile, "IMPORT struct META_STATE_s META_I_STATE, META_N_STATE;\n");

  /* generate externs */
  fprintf (hfile, "extern void start (register STATE_p);\n");
  fprintf (hfile, "extern int goal_situation (register STATE_p);\n");
}


static void
emit_operator (instant_p insts)
{
  cond_p      pp;
  idlist_p    vp;
  instant_p   ip;
  int         i;
  
  /* generating comments */
  fprintf (yfile, "\n\n/* generated code for operator %s with vars: ", global_operator->name);
  fprintf (xfile, "\n\n/* generated code for operator %s with vars: ", global_operator->name);
  for (ip = insts; ip; ip = ip->next)
    {
      fprintf (yfile, "<%s> = %s", ip->var, ip->val);
      fprintf (xfile, "<%s> = %s", ip->var, ip->val);
      if (ip->next)
	{
	  fprintf (yfile, ", ");
	  fprintf (xfile, ", ");
	}
      else
	{
	  fprintf (yfile, " */\n");
	  fprintf (xfile, " */\n");
	}
    }
  
  /* generating new function name */
  fprintf (yfile, "int\n");
  fprintf (yfile, "operator%d (void)\n", opname);
  fprintf (yfile, "{\n");
  fprintf (yfile, "  register int tmp = ");
  fprintf (xfile, "  tmp = ");
  fprintf (zfile, "  operators[%d].name = \"%s(", opname, global_operator->name);
  for (vp = global_vars; vp; vp = vp->next)
    for (ip = insts; ip; ip = ip->next)
      if (!strcmp (vp->name, ip->var))
	{
	  fprintf (zfile, "%s", ip->val);
	  if (vp->next)
	    fprintf (zfile, ",");
	  else
	    fprintf (zfile, ")\";\n");
	}

  /* generating code for tmp variable */
  for (i = 0, pp = global_preconds; pp; i++, pp = pp->next)
    {
      fprintf (yfile, "(%s ", rvalue (pp->lvalue, NULL, insts, "(&I_STATE)"));
      fprintf (yfile, "%c= %s)", (pp->op == EQUAL ? '=' : '!'), rvalue (pp->rvalue, NULL, insts, "(&I_STATE)"));

      fprintf (xfile, "(%s (%s, ", (pp->op == EQUAL ? "fcomm" : "!fcomm"), 
	       rvalue (pp->rvalue, NULL, insts, "(&META_I_STATE)"));
      fprintf (xfile, "%s))", hlvalue (pp->lvalue, NULL, insts, "(&META_I_STATE)"));

      if (pp->next)
	{
	  fprintf (yfile, " && ");
	  fprintf (xfile, " && ");
	}
      else
	{
	  fprintf (yfile, ";\n\n");
	  fprintf (xfile, ";\n\n");
	}
    }

  /* generating code for effects */
  fprintf (yfile, "  if (tmp)\n");
  fprintf (xfile, "  if (tmp)\n");
  fprintf (yfile, "    {\n");
  fprintf (xfile, "    {\n");
  fprintf (xfile, "      cost = 1;\n");
  for (i = 0, pp = global_preconds; pp; i++, pp = pp->next)
    {
      fprintf (xfile, "      cost += %s (%s, ", (pp->op == EQUAL ? "fcost" : "focost"), 
	       rvalue (pp->rvalue, NULL, insts, "(&META_I_STATE)"));
      fprintf (xfile, "%s);\n", hlvalue (pp->lvalue, NULL, insts, "(&META_I_STATE)"));
      if (!pp->next)
	fprintf (xfile, "\n");
    }
  for (pp = global_effects; pp; pp = pp->next)
    {
      fprintf (yfile, "      %s ", lvalue (pp->lvalue, NULL, insts, "(&N_STATE)"));
      fprintf (yfile, "= %s;\n", rvalue (pp->rvalue, NULL, insts, "(&N_STATE)"));

      fprintf (xfile, "      funion (%s, ", rvalue (pp->rvalue, NULL, insts, "(&META_N_STATE)"));
      fprintf (xfile, "%s, ", hlvalue (pp->lvalue, NULL, insts, "(&META_N_STATE)"));
      fprintf (xfile, " %s);\n", hlvalue (pp->lvalue, NULL, insts, "(&META_N_STATE)"));
      fprintf (xfile, "      fucost (cost, %s, ", rvalue (pp->rvalue, NULL, insts, "(&META_N_STATE)"));
      fprintf (xfile, "%s);\n", hlvalue (pp->lvalue, NULL, insts, "(&META_N_STATE)"));
    }
  fprintf (yfile, "    }\n");
  fprintf (xfile, "    }\n");

  /* close function */
  fprintf (yfile, "  return tmp;\n");
  fprintf (yfile, "}\n\n");

  /* increment operator ID */
  opname++;
}


static void
instantiate_operator (operator_p oper, idlist_p vars, cond_p precs, cond_p effects)
{
  global_operator = oper;
  global_preconds = precs;
  global_effects = effects;
  global_vars = vars;
  instantiate_values (vars, NULL, emit_operator);
}


static void
instantiate_values (idlist_p var, instant_p insts, void (*func)(instant_p))
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
