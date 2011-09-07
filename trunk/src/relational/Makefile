CC = gcc
MV = mv
BISON = yacc
PARSER = ./relparser
CFLAGS = -O3

all:
			@echo "**Making all in `pwd`"
			@make my_all

my_all:			$(PARSER) asprelplan.o


$(PARSER):		$(PARSER).tab.c
			$(CC) $(LDFLAGS) -o $@ $(PARSER).tab.c

$(PARSER).tab.c:	$(PARSER).y
			$(BISON) $(PARSER).y
			$(MV) y.tab.c $@

asprelplan.o:		asprelplan.c asprelplan.h
			$(CC) $(CFLAGS) -o $@ -c asprelplan.c

clean:
			@echo "**Making clean in `pwd`"
			rm -f *~ $(PARSER) $(PARSER).tab.c asprelplan.o

install:		$(PARSER) asprelplan.o
			@echo "**Making install in `pwd`"
			cp $(PARSER) ../../bin
			cp asprelplan.o ../../lib
			cp asprelplan.h ../../include
			cp relpro-ope.c ../../include

dist:
			@echo "**Making dist in `pwd`"
			make clean
			make $(PARSER).tab.c
