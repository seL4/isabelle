###############################################
# Title:      Tools/8bit/c-sources/a2isa/Makefile
# ID:         $Id$
# Author:     David von Oheimb
# Copyright   1996 TU Muenchen
#
# Makefile for Isabelle ASCII to 8bit converter
################################################

OBJECTS = main.o lex.o

CC = gcc

# Application name
APPNAME = a2isa

# ----------------------------------------------------

$(APPNAME):  $(OBJECTS)
	$(CC) -o $(APPNAME) $(OBJECTS);	strip $(APPNAME)

lex.o: lex.x
	flex lex.x; $(CC) -c -o lex.o lex.yy.c

# ----------------------------------------------------

clean:
	@echo "     cleaning up object and tmp files..."
	@rm -f *.o lex.yy.c
