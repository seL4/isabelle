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
use     "thy_syntax";

use "~~/src/Provers/Arith/cancel_numerals.ML";
use "~~/src/Provers/Arith/combine_numerals.ML";

use_thy "mono";
use     "ind_syntax.ML";
use     "Tools/cartprod.ML";
use_thy "Fixedpt";
use     "Tools/inductive_package.ML";
use     "Tools/induct_tacs.ML";
use     "Tools/primrec_package.ML";
use_thy "QUniv";
use     "Tools/datatype_package.ML";

use     "Tools/numeral_syntax.ML";
(*the all-in-one theory*)
with_path "Integ" use_thy "Main";

simpset_ref() := simpset() setmksimps (map mk_eq o Ord_atomize o gen_all);

print_depth 8;

Goal "True";  (*leave subgoal package empty*)
