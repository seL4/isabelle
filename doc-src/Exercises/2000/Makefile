#
# $Id$
#
# IsaMakefile for PSV2000
#

SESSIONS = a1

## targets

default: sessions 
sessions: $(SESSIONS)


## a1

a1: a1/generated/session.tex

a1/generated/session.tex: a1/ROOT.ML a1/*.thy 
	isatool make
