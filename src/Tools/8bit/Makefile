###############################################
# Title:      Tools/8bit/Makefile
# ID:         $Id$
# Author:     Franz Regensburger
# Copyright   1996 TU Muenchen
#
# Master Makefile for Isabelle 8bit package
# ATTENTION: this is a GNU-MAKE Makefile
#
# Franz Regensburger <regensbu@informatik.tu-muenchen.de>, 8.3.95
# last changed:
#	21.3.95	
#	02.09.95 added latex2e support	
#       07.02.96 added BASH variable and changed reference to amssym 
#                in amssymb for latex2.09
#       23.05.96 modifications by David von Oheimb
#
###############################################

# operate silently
MAKEFLAGS='s'

###############################################
# general configuration
###############################################

# path and name of bash shell
# should be /bin/bash on every reasonable system 
#
#BASH=/bin/bash
BASH=/bin/bash

# Perl path and name for interpreter
# should be a perl 4.x
#PERL=/usr/bin/perl
PERL=/usr/local/dist/bin/perl

# use LaTeX2e instead of LaTeX 2.09
# this flag is currently only sensible for perl script gen-isadoc
# set to empty string for LaTeX 2.09
USE2E='-2e'

# name of GNU make utility: `make' on linux box; `gmake' on solaris
#GMAKE=make
GMAKE=gmake

#keycode for Super_L       26 on SUN, 64  on Linux box 
#SUPER_L=64
SUPER_L=26

#keycode for Hyper_R       20 on SUN, 113 on Linux box 
#HYPER_R=113
HYPER_R=20

CONFIGFILES = config/Makefile config/key-table.inp config/conv-tables.inp

#path stem to isabelle source, used by patcher
STEM = /usr/wiss/oheimb/isabelle/

###############################################
# configuration for configuration files in ./config
###############################################

CONV_SOURCE_DIR="$(ISABELLE8BIT)/c-sources/isa2latex"

###############################################
# configuration for GNU emacs
###############################################

# Name of your GNU emacs executable 
GNU_ENAME=emacs

#users init file ($HOME is added). This file is loaded after
#the init file isa_gnu_emacs.emacs 
GNU_INIT=.emacs_gnu_isa

###############################################
# configuration for xemacs
###############################################

# Name of your xemacs executable 

XEMACS_ENAME=xemacs

#users init file ($HOME is added). This file is loaded after
#the init file isa_xemacs.emacs 

XEMACS_INIT=.emacs_xemacs_isa

###############################################
# END of Configuration Section 
###############################################


###############################################
# user targets        
###############################################
 
# ----------------------------------------------------

# first target. Used if no target is given by the user
#usage:
#	echo "type 'make install' to install everything"
#	echo "type 'make clean' to cleanup"

# ----------------------------------------------------

all:  $(CONFIGFILES)\
	bin/gen-isa2latex bin/gen-isaterm bin/gen-isavim bin/gen-isaaxe\
	bin/gen-isa_gnu_emacs bin/gen-isa_xemacs bin/gen-isadoc\
	configuration a2isa bin/isa2latex bin/a2isa\
	bin/isa_gnu_emacs bin/isa_xemacs bin/isavim bin/isaaxe\
	bin/isaterm bin/isa_xmosaic bin/isapal bin/codetable bin/patcher\
	fonts/install keyboard/install\
	isa-patches/HOL/add-HOL.cfg isa-patches/HOL/clean-HOL.cfg\
	isa-patches/HOL/extract-HOL.cfg\
	isa-patches/HOLCF/add-HOLCF.cfg isa-patches/HOLCF/clean-HOLCF.cfg\
	isa-patches/HOLCF/extract-HOLCF.cfg\
	manual\

# ----------------------------------------------------

clean:
	cd bin; rm -f a2isa codetable gen-* isa* patcher
	cd c-sources/a2isa; $(GMAKE) clean
	cd c-sources/isa2latex; $(GMAKE) clean
	cd doc; $(GMAKE) clean

###############################################
# internal targets        
###############################################

####### configuration files and the Makefile

$(CONFIGFILES): Makefile
	@echo "configuring the configuration files"
	@cd config;\
	$(PERL) -pi \
		-e "s#^USE2E\s*=.*#USE2E= $(USE2E)#g;" \
		-e "s#^GMAKE\s*=.*#GMAKE= $(GMAKE)#g;" \
		Makefile
	@cd config;\
	$(PERL) -pi \
		-e "s#^BIN_DIR\s*\".*#BIN_DIR \"$(CONV_BIN_DIR)\"#g;" \
		key-table.inp
	@cd config;\
	$(PERL) -pi \
	-e "s#^CONV_SOURCE_DIR\s*\".*#CONV_SOURCE_DIR \"$(CONV_SOURCE_DIR)\"#g;" \
	 conv-tables.inp

#######      Generators        

# ----------------------------------------------------
	
bin/gen-isa2latex: Makefile #perl/generators/gen-isa2latex.pl
	@echo "configuring gen-isa2latex"
	@cd perl/generators;\
	$(PERL) -pi \
		-e "s#GMAKE\s*=.*#GMAKE= \"$(GMAKE)\";#g;" \
		-e "s&^#!.*&#!$(PERL)&g;" \
		gen-isa2latex.pl
	@rm -f bin/gen-isa2latex;\
	ln -s ../perl/generators/gen-isa2latex.pl bin/gen-isa2latex

# ----------------------------------------------------
	
bin/gen-isaterm: Makefile #perl/generators/gen-isaterm.pl
	@echo "configuring gen-isaterm"
	@cd perl/generators;\
	$(PERL) -pi \
		-e "s&^#!.*&#!$(PERL)&g;" \
		gen-isaterm.pl
	@rm -f bin/gen-isaterm;\
	ln -s ../perl/generators/gen-isaterm.pl bin/gen-isaterm

# ----------------------------------------------------
	
bin/gen-isavim: Makefile #perl/generators/gen-isavim.pl
	@echo "configuring gen-isavim"
	@cd perl/generators;\
	$(PERL) -pi \
		-e "s&^#!.*&#!$(PERL)&g;" \
		gen-isavim.pl
	@rm -f bin/gen-isavim;\
	ln -s ../perl/generators/gen-isavim.pl bin/gen-isavim

# ----------------------------------------------------
	
bin/gen-isaaxe: Makefile #perl/generators/gen-isaaxe.pl
	@echo "configuring gen-isaaxe"
	@cd perl/generators;\
	$(PERL) -pi \
		-e "s&^#!.*&#!$(PERL)&g;" \
		gen-isaaxe.pl
	@rm -f bin/gen-isaaxe;\
	ln -s ../perl/generators/gen-isaaxe.pl bin/gen-isaaxe

# ----------------------------------------------------
	
bin/gen-isa_gnu_emacs: Makefile #perl/generators/gen-isa_gnu_emacs.pl
	@echo "configuring gen-isa_gnu_emacs"
	@cd perl/generators;\
	$(PERL) -pi \
		-e "s&^#!.*&#!$(PERL)&g;" \
		gen-isa_gnu_emacs.pl
	@rm -f bin/gen-isa_gnu_emacs;\
	ln -s ../perl/generators/gen-isa_gnu_emacs.pl bin/gen-isa_gnu_emacs

# ----------------------------------------------------
	
bin/gen-isa_xemacs: Makefile #perl/generators/gen-isa_xemacs.pl
	@echo "configuring gen-isa_xemacs"
	@cd perl/generators;\
	$(PERL) -pi \
		-e "s&^#!.*&#!$(PERL)&g;" \
		gen-isa_xemacs.pl
	@rm -f bin/gen-isa_xemacs;\
	ln -s ../perl/generators/gen-isa_xemacs.pl bin/gen-isa_xemacs

# ----------------------------------------------------
	
bin/gen-isadoc: Makefile #perl/generators/gen-isadoc.pl
	@echo "configuring gen-isadoc"
	@cd perl/generators;\
	$(PERL) -pi \
		-e "s&^#!.*&#!$(PERL)&g;" \
		gen-isadoc.pl
	@rm -f bin/gen-isadoc;\
	ln -s ../perl/generators/gen-isadoc.pl bin/gen-isadoc


#######      Converter        

# ----------------------------------------------------
	
#isa2latex, editor support, font documentation:
configuration:
	@cd config; $(GMAKE)

a2isa:
	@cd c-sources/a2isa; $(GMAKE); $(GMAKE) clean

bin/isa2latex: c-sources/isa2latex/isa2latex
	@echo "installing isa2latex"
	@rm -f bin/isa2latex;\
	ln -s ../c-sources/isa2latex/isa2latex bin/isa2latex

bin/a2isa: c-sources/a2isa/a2isa
	@echo "installing a2isa"
	@rm -f bin/a2isa;\
	ln -s ../c-sources/a2isa/a2isa bin/a2isa

#######      Editors        

# ----------------------------------------------------
	
bin/isa_gnu_emacs: Makefile #gnu_emacs/isa_gnu_emacs
	@echo "installing GNU emacs"
	@cd gnu_emacs;\
	$(PERL) -pi \
		-e "s&^#!.*&#!$(BASH)&g;" \
		-e "s#^ENAME\s*=.*#ENAME=$(GNU_ENAME)#g;"\
		-e "s#^INIT\s*=.*#INIT=$(GNU_INIT)#g;" \
		isa_gnu_emacs
	@rm -f bin/isa_gnu_emacs;\
	ln -s ../gnu_emacs/isa_gnu_emacs bin/isa_gnu_emacs

# ----------------------------------------------------
	
bin/isa_xemacs: Makefile #xemacs/isa_xemacs
	@echo "installing xemacs"
	@@cd xemacs;\
	$(PERL) -pi\
		-e "s&^#!.*&#!$(BASH)&g;" \
		-e "s#^ENAME\s*=.*#ENAME=$(XEMACS_ENAME)#g;"\
		-e "s#^INIT\s*=.*#INIT=$(XEMACS_INIT)#g;" \
		isa_xemacs
	@rm -f bin/isa_xemacs;\
	ln -s ../xemacs/isa_xemacs bin/isa_xemacs

# ----------------------------------------------------
	
bin/isavim: Makefile #vim/isavim
	@echo "installing vim"
	@@cd vim;\
	$(PERL) -pi\
		-e "s&^#!.*&#!$(BASH)&g;" \
		initvim ; \
	$(PERL) -pi\
		-e "s&^#!.*&#!$(BASH)&g;" \
		isavim
	@rm -f bin/isavim;\
	ln -s ../vim/isavim bin/isavim

# ----------------------------------------------------
	
bin/isaaxe: Makefile #axe/isaaxe
	@echo "installing axe"
	@cd axe;\
	$(PERL) -pi \
		-e "s&^#!.*&#!$(BASH)&g;" \
		isaaxe
	@rm -f bin/isaaxe;\
	ln -s ../axe/isaaxe bin/isaaxe

# ----------------------------------------------------
	
bin/isa_xmosaic: Makefile #xmosaic/isa_xmosaic
	@echo "installing xmosaic"
	@cd xmosaic;\
	$(PERL) -pi\
		-e "s&^#!.*&#!$(BASH)&g;" \
		isa_xmosaic
	@rm -f bin/isa_xmosaic;\
	ln -s ../xmosaic/isa_xmosaic bin/isa_xmosaic

#######      Terminal        

# ----------------------------------------------------

bin/isaterm: Makefile #term/isaterm
	@echo "installing term"
	@cd term;\
	$(PERL) -pi\
		-e "s&^#!.*&#!$(BASH)&g;" \
		initisaterm;\
	$(PERL) -pi\
		-e "s&^#!.*&#!$(BASH)&g;" \
		isaterm
	@rm -f bin/isaterm;\
	ln -s ../term/isaterm bin/isaterm	

#######      other perl scripts

# ----------------------------------------------------

bin/isapal: Makefile #perl/isapal.pl
	@echo "installing perl script isapal"
	@cd perl;\
	$(PERL) -pi \
		-e "s&^#!.*&#!$(PERL)&g;"\
		isapal.pl
	@rm -f bin/isapal;\
	ln -s ../perl/isapal.pl bin/isapal

bin/codetable: Makefile #perl/codetable.pl
	@echo "installing perl script codetable"
	@cd perl;\
	$(PERL) -pi \
		-e "s&^#!.*&#!$(PERL)&g;" \
		codetable.pl
	@rm -f bin/codetable;\
	ln -s ../perl/codetable.pl bin/codetable

bin/patcher: Makefile #perl/patcher.pl
	@echo "installing perl script patcher"
	@cd perl;\
	$(PERL) -pi \
	-e "s&^#!.*&#!$(PERL)&g;" \
	patcher.pl
	@rm -f bin/patcher;\
	ln -s ../perl/patcher.pl bin/patcher

fonts/install: Makefile
	@cd fonts;\
	$(PERL) -pi\
		-e "s&^#!.*&#!$(BASH)&g;" \
		install

keyboard/install: Makefile
	@cd keyboard;\
	$(PERL) -pi\
		-e "s&^#!.*&#!$(BASH)&g;" \
		-e "s#^SUPER_L\s*=.*#SUPER_L=$(SUPER_L)#g;"\
		-e "s#^HYPER_R\s*=.*#HYPER_R=$(HYPER_R)#g;"\
		install

isa-patches/HOL/add-HOL.cfg: Makefile
	@cd isa-patches/HOL;\
	$(PERL) -pi -e "s#^STEM\s*\".*#STEM \"$(STEM)\"#g;" add-HOL.cfg
isa-patches/HOL/clean-HOL.cfg: Makefile
	@cd isa-patches/HOL;\
	$(PERL) -pi -e "s#^STEM\s*\".*#STEM \"$(STEM)\"#g;" clean-HOL.cfg
isa-patches/HOL/extract-HOL.cfg: Makefile
	@cd isa-patches/HOL;\
	$(PERL) -pi -e "s#^STEM\s*\".*#STEM \"$(STEM)\"#g;" extract-HOL.cfg
isa-patches/HOLCF/add-HOLCF.cfg: Makefile
	@cd isa-patches/HOLCF;\
	$(PERL) -pi -e "s#^STEM\s*\".*#STEM \"$(STEM)\"#g;" add-HOLCF.cfg
isa-patches/HOLCF/clean-HOLCF.cfg: Makefile
	@cd isa-patches/HOLCF;\
	$(PERL) -pi -e "s#^STEM\s*\".*#STEM \"$(STEM)\"#g;" clean-HOLCF.cfg
isa-patches/HOLCF/extract-HOLCF.cfg: Makefile
	@cd isa-patches/HOLCF;\
	$(PERL) -pi -e "s#^STEM\s*\".*#STEM \"$(STEM)\"#g;" extract-HOLCF.cfg

# ----------------------------------------------------

manual:
	@cd doc; $(GMAKE) manual.dvi
