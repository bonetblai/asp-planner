CC = gcc
MV = mv
BISON = yacc
PARSER = ./funparser
CFLAGS = -O3 

all:
			@echo "**Making all in `pwd`"
			@make my_all

my_all:			fset.o


fset.o:			fset.c fset.h
			$(CC) $(CFLAGS) -c fset.c

clean:
			@echo "**Making clean in `pwd`"
			rm -f *~ fset.o

install:		fset.o
			@echo "**Making install in `pwd`"
			cp fset.o ../../lib
			cp fset.h ../../include

dist:
			@echo "**Making dist in `pwd`"
			make clean
