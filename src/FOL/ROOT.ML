(*  Title: 	FOL/ROOT
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Adds First-Order Logic to a database containing pure Isabelle. 
Should be executed in the subdirectory FOL.
*)

val banner = "First-Order Logic with Natural Deduction";

writeln banner;

init_thy_reader();

print_depth 1;  
use_thy "FOL";

use "../Provers/simplifier.ML";
use "../Provers/splitter.ML";
use "../Provers/ind.ML";
use "../Provers/hypsubst.ML";
use "../Provers/classical.ML";

(*** Applying HypsubstFun to generate hyp_subst_tac ***)

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

(*** Applying ClassicalFun to create a classical prover ***)
structure Classical_Data = 
  struct
  val sizef	= size_of_thm
  val mp	= mp
  val not_elim	= notE
  val classical	= classical
  val hyp_subst_tacs=[hyp_subst_tac]
  end;

structure Cla = ClassicalFun(Classical_Data);
open Cla;

(*Propositional rules 
  -- iffCE might seem better, but in the examples in ex/cla
     run about 7% slower than with iffE*)
val prop_cs = empty_cs addSIs [refl,TrueI,conjI,disjCI,impI,notI,iffI] 
                       addSEs [conjE,disjE,impCE,FalseE,iffE];

(*Quantifier rules*)
val FOL_cs = prop_cs addSIs [allI] addIs [exI,ex1I] 
                     addSEs [exE,ex1E] addEs [allE];

val ex1_functional = prove_goal FOL.thy
    "!!a b c. [| EX! z. P(a,z);  P(a,b);  P(a,c) |] ==> b = c"
 (fn _ => [ (deepen_tac FOL_cs 0 1) ]);

use "simpdata.ML";

use "../Pure/install_pp.ML";
print_depth 8;

val FOL_build_completed = ();	(*indicate successful build*)

