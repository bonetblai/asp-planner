CC = gcc
MV = mv
CFLAGS = -I../../include -I.
PARSER = ../../bin/relparser
FSET = ../../lib/fset.o
ASPPLAN = ../../lib/asprelplan.o
OBJS = $(FSET) $(ASPPLAN)
EXAMPLES = sussman rocket1 rocket2 logistics1 logistics2 logistics3 \
           blocks1 blocks2 blocks3 blocks4 blocks5


all:
		@echo "**Making all in `pwd`"
		@make my_all

my_all:		$(EXAMPLES)



#  Sussman's Anomaly

sussman:	sussman.ope.o sussman.fac.o sussman.tab.o $(FSET)
		$(CC) -O3 -o $@ $@.ope.o $@.fac.o $@.tab.o $(OBJS)


#  Rocket Domain

rocket1:	rocket1.ope.o rocket1.fac.o rocket1.tab.o $(OBJS)
		$(CC) -O3 -o $@ $@.ope.o $@.fac.o $@.tab.o $(OBJS)

rocket2:	rocket2.ope.o rocket2.fac.o rocket2.tab.o $(FSET)
		$(CC) -O3 -o $@ $@.ope.o $@.fac.o $@.tab.o $(OBJS)


#  Logistics Domain

logistics1:	logistics1.ope.o logistics1.fac.o logistics1.tab.o $(FSET)
		$(CC) -O3 -o $@ $@.ope.o $@.fac.o $@.tab.o $(OBJS)

logistics2:	logistics2.ope.o logistics2.fac.o logistics2.tab.o $(FSET)
		$(CC) -O3 -o $@ $@.ope.o $@.fac.o $@.tab.o $(OBJS)

logistics3:	logistics3.ope.o logistics3.fac.o logistics3.tab.o $(FSET)
		$(CC) -O3 -o $@ $@.ope.o $@.fac.o $@.tab.o $(OBJS)


#  Blocks World Domain

blocks1:	blocks1.ope.o blocks1.fac.o blocks1.tab.o $(FSET)
		$(CC) -O3 -o $@ $@.ope.o $@.fac.o $@.tab.o $(OBJS)

blocks2:	blocks2.ope.o blocks2.fac.o blocks2.tab.o $(FSET)
		$(CC) -O3 -o $@ $@.ope.o $@.fac.o $@.tab.o $(OBJS)

blocks3:	blocks3.ope.o blocks3.fac.o blocks3.tab.o $(FSET)
		$(CC) -O3 -o $@ $@.ope.o $@.fac.o $@.tab.o $(OBJS)

blocks4:	blocks4.ope.o blocks4.fac.o blocks4.tab.o $(FSET)
		$(CC) -O3 -o $@ $@.ope.o $@.fac.o $@.tab.o $(OBJS)

blocks5:	blocks5.ope.o blocks5.fac.o blocks5.tab.o $(FSET)
		$(CC) -O3 -o $@ $@.ope.o $@.fac.o $@.tab.o $(OBJS)



sussman.ope.c sussman.fac.c sussman.tab.c:	\
		sussman.ops sussman.facts
		$(PARSER) $(@:.ope.c=) $(@:.ope.c=).facts $(@:.ope.c=).ops
		$(MV) $(@:.ope.c=)1.c $(@:.ope.c=).ope.c
		$(MV) $(@:.ope.c=)2.c $(@:.ope.c=).fac.c
		$(MV) $(@:.ope.c=)3.c $(@:.ope.c=).tab.c

rocket1.ope.c rocket1.fac.c rocket1.tab.c:	\
		rocket1.ops rocket1.facts
		$(PARSER) $(@:.ope.c=) $(@:.ope.c=).facts $(@:.ope.c=).ops
		$(MV) $(@:.ope.c=)1.c $(@:.ope.c=).ope.c
		$(MV) $(@:.ope.c=)2.c $(@:.ope.c=).fac.c
		$(MV) $(@:.ope.c=)3.c $(@:.ope.c=).tab.c

rocket2.ope.c rocket2.fac.c rocket2.tab.c:	\
		rocket2.ops rocket2.facts
		$(PARSER) $(@:.ope.c=) $(@:.ope.c=).facts $(@:.ope.c=).ops
		$(MV) $(@:.ope.c=)1.c $(@:.ope.c=).ope.c
		$(MV) $(@:.ope.c=)2.c $(@:.ope.c=).fac.c
		$(MV) $(@:.ope.c=)3.c $(@:.ope.c=).tab.c

logistics1.ope.c logistics1.fac.c logistics1.tab.c:	\
			logistics1.ops logistics1.facts
			$(PARSER) $(@:.ope.c=) $(@:.ope.c=).facts $(@:.ope.c=).ops
			$(MV) $(@:.ope.c=)1.c $(@:.ope.c=).ope.c
			$(MV) $(@:.ope.c=)2.c $(@:.ope.c=).fac.c
			$(MV) $(@:.ope.c=)3.c $(@:.ope.c=).tab.c

logistics2.ope.c logistics2.fac.c logistics2.tab.c:	\
			logistics2.ops logistics2.facts
			$(PARSER) $(@:.ope.c=) $(@:.ope.c=).facts $(@:.ope.c=).ops
			$(MV) $(@:.ope.c=)1.c $(@:.ope.c=).ope.c
			$(MV) $(@:.ope.c=)2.c $(@:.ope.c=).fac.c
			$(MV) $(@:.ope.c=)3.c $(@:.ope.c=).tab.c

logistics3.ope.c logistics3.fac.c logistics3.tab.c:	\
			logistics3.ops logistics3.facts
			$(PARSER) $(@:.ope.c=) $(@:.ope.c=).facts $(@:.ope.c=).ops
			$(MV) $(@:.ope.c=)1.c $(@:.ope.c=).ope.c
			$(MV) $(@:.ope.c=)2.c $(@:.ope.c=).fac.c
			$(MV) $(@:.ope.c=)3.c $(@:.ope.c=).tab.c

blocks1.ope.c blocks1.fac.c blocks1.tab.c:	\
		blocks1.ops blocks1.facts
		$(PARSER) $(@:.ope.c=) $(@:.ope.c=).facts $(@:.ope.c=).ops
		$(MV) $(@:.ope.c=)1.c $(@:.ope.c=).ope.c
		$(MV) $(@:.ope.c=)2.c $(@:.ope.c=).fac.c
		$(MV) $(@:.ope.c=)3.c $(@:.ope.c=).tab.c

blocks2.ope.c blocks2.fac.c blocks2.tab.c:	\
		blocks2.ops blocks2.facts
		$(PARSER) $(@:.ope.c=) $(@:.ope.c=).facts $(@:.ope.c=).ops
		$(MV) $(@:.ope.c=)1.c $(@:.ope.c=).ope.c
		$(MV) $(@:.ope.c=)2.c $(@:.ope.c=).fac.c
		$(MV) $(@:.ope.c=)3.c $(@:.ope.c=).tab.c

blocks3.ope.c blocks3.fac.c blocks3.tab.c:	\
		blocks3.ops blocks3.facts
		$(PARSER) $(@:.ope.c=) $(@:.ope.c=).facts $(@:.ope.c=).ops
		$(MV) $(@:.ope.c=)1.c $(@:.ope.c=).ope.c
		$(MV) $(@:.ope.c=)2.c $(@:.ope.c=).fac.c
		$(MV) $(@:.ope.c=)3.c $(@:.ope.c=).tab.c

blocks4.ope.c blocks4.fac.c blocks4.tab.c:	\
		blocks4.ops blocks4.facts
		$(PARSER) $(@:.ope.c=) $(@:.ope.c=).facts $(@:.ope.c=).ops
		$(MV) $(@:.ope.c=)1.c $(@:.ope.c=).ope.c
		$(MV) $(@:.ope.c=)2.c $(@:.ope.c=).fac.c
		$(MV) $(@:.ope.c=)3.c $(@:.ope.c=).tab.c

blocks5.ope.c blocks5.fac.c blocks5.tab.c:	\
		blocks5.ops blocks5.facts
		$(PARSER) $(@:.ope.c=) $(@:.ope.c=).facts $(@:.ope.c=).ops
		$(MV) $(@:.ope.c=)1.c $(@:.ope.c=).ope.c
		$(MV) $(@:.ope.c=)2.c $(@:.ope.c=).fac.c
		$(MV) $(@:.ope.c=)3.c $(@:.ope.c=).tab.c



.c.o:
		$(CC) $(CFLAGS) -c $<

.ope.c.ope.o:
		$(CC) $(CFLAGS) -c $< $(DFLAGS)

.fac.c.fac.o:
		$(CC) $(CFLAGS) -c $< $(DFLAGS)

.tab.c.tab.o:
		$(CC) $(CFLAGS) -O3 -c $< $(DFLAGS)

clean:
		@echo "Making clean in `pwd`"
		rm -f *~ *.o *.h *.c $(EXAMPLES)

dist:
		@echo "Making dist in `pwd`"
		make clean
