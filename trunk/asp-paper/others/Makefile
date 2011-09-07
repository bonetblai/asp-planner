CC = gcc
MV = mv
CFLAGS = -I../../include -I. -g
PARSER = ../../bin/funparser
FSET = ../../lib/fset.o
ASPPLAN = aspfunplan.c
OBJS = $(FSET) aspfunplan.o
EXAMPLES = puzzle


all:
		@echo "**Making all in `pwd`"
		@make my_all

my_all:		$(EXAMPLES)



#  8 Puzzle

puzzle:		puzzle.h puzzle.ope.o puzzle.fac.o puzzle.tab.o $(FSET) $(ASPPLAN)
		$(CC) -g -c $(ASPPLAN) -DINCFILE=\"$@.h\" $(CFLAGS)
		$(CC) -o $@ $@.ope.o $@.fac.o $@.tab.o $(OBJS)
		rm aspfunplan.o



puzzle.h:	puzzle.ops puzzle.facts
		$(PARSER) $(@:.h=) $(@:.h=).facts $(@:.h=).ops
		$(MV) $(@:.h=)1.c $(@:.h=).ope.c
		$(MV) $(@:.h=)2.c $(@:.h=).fac.c
		$(MV) $(@:.h=)3.c $(@:.h=).tab.c



.c.o:
		$(CC) $(CFLAGS) -c $<

puzzle.ope.o:	puzzle.ope.c
		$(CC) $(CFLAGS) -c puzzle.ope.c $(DFLAGS)

puzzle.fac.o:	puzzle.fac.c
		$(CC) $(CFLAGS) -c puzzle.fac.c $(DFLAGS)

puzzle.tab.o:	puzzle.tab.c
		$(CC) $(CFLAGS) -c puzzle.tab.c $(DFLAGS)

clean:
		@echo "Making clean in `pwd`"
		rm -f *~ *.o *.h $(EXAMPLES) puzzle.ope.c puzzle.tab.c puzzle.fac.c

dist:
		@echo "Making dist in `pwd`"
		make clean
