###############################################
# Title:      Tools/8bit/c-sources/a2isa/Makefile
# ID:         $Id$
# Author:     David von Oheimb
# Copyright   1996 TU Muenchen
#
# Makefile for Isabelle ASCII to 8bit converter
################################################

AOBJECTS  = main.o  lex.o
AXOBJECTS = main.o xlex.o

CC = gcc

.SUFFIXES: $(SUFFIXES) .x

.x.o:
	flex $<; $(CC) -c -o $@ lex.yy.c

# ----------------------------------------------------

all: a2isa ax2isa

a2isa:  $(AOBJECTS)
	$(CC) -o a2isa $(AOBJECTS); strip a2isa

ax2isa: $(AXOBJECTS)
	$(CC) -o ax2isa $(AXOBJECTS); strip ax2isa

#lex.o: lex.x
#	flex lex.x; $(CC) -c -o lex.o lex.yy.c

# ----------------------------------------------------

clean:
	@echo "     cleaning up object and tmp files..."
	@rm -f *.o lex.yy.c
