(*  Title:      FOL/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Adds First-Order Logic to a database containing pure Isabelle. 
Should be executed in the subdirectory FOL.
*)

val banner = "First-Order Logic with Natural Deduction";

writeln banner;

init_thy_reader();

print_depth 1;  

use "../Provers/splitter.ML";
use "../Provers/ind.ML";
use "../Provers/hypsubst.ML";
use "../Provers/classical.ML";

use_thy "IFOL";

structure Hypsubst_Data =
  struct
  structure Simplifier = Simplifier
    (*Take apart an equality judgement; otherwise raise Match!*)
  fun dest_eq (Const("Trueprop",_) $ (Const("op =",_)  $ t $ u)) = (t,u)
  val eq_reflection = eq_reflection
  val imp_intr = impI
  val rev_mp = rev_mp
  val subst = subst
  val sym = sym
  end;

structure Hypsubst = HypsubstFun(Hypsubst_Data);
open Hypsubst;


use "intprover.ML";

use_thy "FOL";

qed_goal "ex1_functional" FOL.thy
    "!!a b c. [| EX! z. P(a,z);  P(a,b);  P(a,c) |] ==> b = c"
 (fn _ => [ (deepen_tac FOL_cs 0 1) ]);


init_pps ();
print_depth 8;

val FOL_build_completed = ();   (*indicate successful build*)
