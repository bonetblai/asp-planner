CC = gcc
MV = mv
BISON = yacc
PARSER = ./funparser
CFLAGS = -O3 

all:
			@echo "**Making all in `pwd`"
			@make my_all

my_all:			$(PARSER)


$(PARSER):		$(PARSER).tab.c
			$(CC) $(CFLAGS) -o $@ $(PARSER).tab.c

$(PARSER).tab.c:	$(PARSER).y
			$(BISON) $(PARSER).y
			$(MV) y.tab.c $@

clean:
			@echo "**Making clean in `pwd`"
			rm -f *~ $(PARSER) $(PARSER).tab.c fset.o

install:		$(PARSER) aspfunplan.c aspfunplan.h
			@echo "**Making install in `pwd`"
			cp $(PARSER) ../../bin
			cp aspfunplan.c ../../lib
			cp aspfunplan.h ../../include

dist:
			@echo "**Making dist in `pwd`"
			make clean
			make $(PARSER).tab.c
