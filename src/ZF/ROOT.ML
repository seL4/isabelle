(*  Title:      ZF/ROOT.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Zermelo-Fraenkel Set Theory on top of classical First-Order Logic.
This theory is the work of Martin Coen, Philippe Noel and Lawrence
Paulson.
*)

val banner = "ZF Set Theory (in FOL)";
writeln banner;

reset eta_contract;

print_depth 1;

(*syntax for old-style theory sections*)
use "thy_syntax";

use "~~/src/Provers/Arith/cancel_numerals.ML";
use "~~/src/Provers/Arith/combine_numerals.ML";

use_thy "mono";
use "ind_syntax.ML";
use_thy "Datatype";

use     "Tools/numeral_syntax.ML";
(*the all-in-one theory*)
with_path "Integ" use_thy "Main";

simpset_ref() := simpset() setmksimps (map mk_eq o Ord_atomize o gen_all);

print_depth 8;

Goal "True";  (*leave subgoal package empty*)
