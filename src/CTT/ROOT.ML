(*  Title:      CTT/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Adds Constructive Type Theory to a database containing pure Isabelle. 
Should be executed in the subdirectory CTT.
*)

val banner = "Constructive Type Theory";
writeln banner;

use_thy "Main";

Goal "tt : T";  (*leave subgoal package empty*)
