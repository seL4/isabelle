#!/bin/csh
# Executed from the main Isabelle directory, this script transfers all
# files needed for the HTML version of Isabelle's theories to the HTTP
# server.
# If you don't want to copy all the logics, you can supply the names of
# the wanted ones as parameters as in "install_html.sh HOL HOLCF".

if ( "$*" == "" ) then
  rsh hpbroy12 "rm -r .html-data/isabelle/*; mkdir .html-data/isabelle/Tools"
endif

rcp index.html hpbroy12:.html-data/isabelle
rcp Tools/*_arrow.gif hpbroy12:.html-data/isabelle/Tools

if ( "$*" == "" ) then
  rcp -r CCL CTT Cube FOL FOLP HOL HOLCF LCF LK Modal ZF \
         hpbroy12:.html-data/isabelle
else
  rcp -r $* hpbroy12:.html-data/isabelle
endif
