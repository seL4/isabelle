(*  Title:      FOL/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Adds First-Order Logic to a database containing pure Isabelle. 
Should be executed in the subdirectory FOL.
*)

val banner = "First-Order Logic with Natural Deduction";

writeln banner;

print_depth 1;  

use "../Provers/simplifier.ML";
use "../Provers/splitter.ML";
use "../Provers/ind.ML";
use "../Provers/hypsubst.ML";
use "../Provers/classical.ML";
use "../Provers/blast.ML";

use_thy "IFOL";

(** Applying HypsubstFun to generate hyp_subst_tac **)
structure Hypsubst_Data =
  struct
  structure Simplifier = Simplifier
    (*Take apart an equality judgement; otherwise raise Match!*)
  fun dest_eq (Const("Trueprop",_) $ (Const("op =",T)  $ t $ u)) = 
	(t, u, domain_type T)
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

use "cladata.ML";
use "simpdata.ML";

qed_goal "ex1_functional" FOL.thy
    "!!a b c. [| EX! z. P(a,z);  P(a,b);  P(a,c) |] ==> b = c"
 (fn _ => [ (deepen_tac FOL_cs 0 1) ]);


print_depth 8;

val FOL_build_completed = ();   (*indicate successful build*)
