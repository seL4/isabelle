###############################################
# Title:      Tools/8bit/config/Makefile
# ID:         $Id$
# Author:     Franz Regensburger
# Copyright   1996 TU Muenchen
#
# Makefile for all the files that depend on the
# configuration files 
#	conv-tables.inp and key-table.inp 
#
# ATTENTION: this is a GNU-MAKE Makefile
#
# Franz Regensburger <regensbu@informatik.tu-muenchen.de> 22.3.95
###############################################

# operate silently
MAKEFLAGS='s'

USE2E= '-2e'

FONTDOCFILES = ../doc/fontindex.dvi ../doc/keyindex.dvi ../doc/fkmatrix.dvi
# the dependent files
FILES =  ../c-sources/isa2latex/conv-lex.x isa2latex\
	../term/isaterm ../vim/isavim ../axe/isaaxe \
	../gnu_emacs/isa_gnu_emacs.emacs ../xemacs/isa_xemacs.emacs \
	$(FONTDOCFILES)

precious: $(FILES)

../c-sources/isa2latex/conv-lex.x: conv-tables.inp
		@echo "generating isa2latex"
		../bin/gen-isa2latex conv-tables.inp 

isa2latex: 
		@cd ../c-sources/isa2latex;\
		gmake

../term/isaterm: key-table.inp
		@echo "generating isaterm"
		../bin/gen-isaterm key-table.inp 

../vim/isavim: key-table.inp
		@echo "generating isavim"
		../bin/gen-isavim key-table.inp 

../axe/isaaxe: key-table.inp
		@echo "generating isaaxe"
		../bin/gen-isaaxe key-table.inp 
	
../gnu_emacs/isa_gnu_emacs.emacs: key-table.inp
		@echo "generating isa_gnu_emacs"
		../bin/gen-isa_gnu_emacs key-table.inp 

../xemacs/isa_xemacs.emacs: key-table.inp
		@echo "generating isa_xemacs"
		../bin/gen-isa_xemacs key-table.inp 

$(FONTDOCFILES): conv-tables.inp key-table.inp 
		@echo "generating documentation"
		../bin/gen-isadoc $(USE2E) conv-tables.inp key-table.inp 

