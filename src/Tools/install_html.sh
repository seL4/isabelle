#!/bin/csh
# Executed from the main Isabelle directory, this script transfers all
# files needed for the HTML version of Isabelle's theories to the HTTP
# server.

rsh www4 "rm -r .html-data/isabelle/*; mkdir .html-data/isabelle/Tools"
rcp index.html www4:.html-data/isabelle
rcp Tools/*_arrow.gif www4:.html-data/isabelle/Tools
rcp -r CCL CTT Cube FOL FOLP HOL HOLCF LCF LK Modal ZF www4:.html-data/isabelle
