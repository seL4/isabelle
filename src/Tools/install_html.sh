#!/bin/csh
# Executed from the main Isabelle directory, this script transfers all
# files needed for the HTML version of Isabelle's theories to the HTTP
# server.
# If you don't want to copy all the logics, you can supply the names of
# the wanted ones as parameters as in "install_html.sh HOL HOLCF".

if ( "$*" == "" ) then
  rsh www4 "rm -r .html-data/isabelle/*; mkdir .html-data/isabelle/Tools; \
            chmod og-w .html-data/isabelle/Tools"
endif

rcp index.html www4:.html-data/isabelle
rcp Tools/*_arrow.gif www4:.html-data/isabelle/Tools

if ( "$*" == "" ) then
  rcp -r CCL CTT Cube FOL FOLP HOL HOLCF LCF LK Modal ZF \
         www4:.html-data/isabelle
else
  rcp -r $* www4:.html-data/isabelle
endif
rsh www4 "chgrp -R isabelle .html-data/isabelle/*;                                       chmod -R g+w .html-data/isabelle/*"
