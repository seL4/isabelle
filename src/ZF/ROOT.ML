(*  Title:      ZF/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Adds Zermelo-Fraenkel Set Theory to a database containing First-Order Logic.

This theory is the work of Martin Coen, Philippe Noel and Lawrence Paulson.
*)

val banner = "ZF Set Theory (in FOL)";
writeln banner;

eta_contract:=false;

print_depth 1;

(*Add user sections for inductive/datatype definitions*)
use     "~~/src/Pure/section_utils";
use     "thy_syntax";

use_thy "Let";
use_thy "ZF";
use     "Tools/typechk";
use_thy "mono";
use     "ind_syntax";
use     "Tools/cartprod";
use_thy "Fixedpt";
use     "Tools/inductive_package";
use_thy "Inductive";
use     "Tools/induct_tacs";
use     "Tools/primrec_package";
use_thy "QUniv";
use     "Tools/datatype_package";
use_thy "Datatype";
use_thy "InfDatatype";
use_thy "List";

(*Integers & binary integer arithmetic*)
cd "Integ";
use_thy "Bin";
cd "..";

(*the all-in-one theory*)
use_thy "Main";

simpset_ref() := simpset() setmksimps (map mk_eq o Ord_atomize o gen_all);

print_depth 8;

Goal "True";  (*leave subgoal package empty*)
