###############################################
# Title:      Tools/8bit/c-sources/isa2latex/Makefile
# ID:         $Id$
# Author:     David von Oheimb
# Copyright   1996 TU Muenchen
#
# Makefile for Isabelle converter
# 30.3.92 by David von Oheimb
# adjusted for isabelle converter: 22.2.95 by Franz Regensburger
###############################################


# Object files:
OBJECTS = conv-main.o conv-lex.o conv-translate.o

# Source files:
SOURCES = conv-main.c conv-lex.x conv-translate.c

# Compiler:
CC = gcc

# Application name
APPNAME=isa2latex

# ----------------------------------------------------

$(APPNAME):   $(OBJECTS)
	$(CC) -o $(APPNAME) $(OBJECTS); strip $(APPNAME)

conv-main.o: conv-main.c conv-defs.h conv-tables.h
	$(CC) -c conv-main.c

conv-lex.o: conv-lex.x conv-defs.h conv-tables.h
	flex -8 -t conv-lex.x | cat >tmp.c ; $(CC) -c -o conv-lex.o tmp.c

#conv-lex.x:  ../../config/conv-tables.inp
#	touch conv-lex.x

conv-translate.o: conv-translate.c conv-defs.h
	$(CC) -c conv-translate.c

# ----------------------------------------------------

clean:
	@rm -f *.o tmp.c tmp.txt
