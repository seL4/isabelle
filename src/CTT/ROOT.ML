(*  Title:      CTT/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Adds Constructive Type Theory to a database containing pure Isabelle. 
Should be executed in the subdirectory CTT.
*)

val banner = "Constructive Type Theory";
writeln banner;

print_depth 1;  

use_thy "CTT";
use "~~/src/Provers/typedsimp.ML";
use "rew.ML";
use_thy "Main";

print_depth 8;

Goal "tt : T";  (*leave subgoal package empty*)
