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

use "../Provers/hypsubst.ML";
use "../Provers/classical.ML";
use "../Provers/simplifier.ML";
use "../Provers/splitter.ML";
use "../Provers/ind.ML";

(*** Applying HypsubstFun to generate hyp_subst_tac ***)

structure Hypsubst_Data =
  struct
  (*Take apart an equality judgement; otherwise raise Match!*)
  fun dest_eq (Const("Trueprop",_) $ (Const("op =",_)  $ t $ u)) = (t,u);

  val imp_intr = impI

  (*etac rev_cut_eq moves an equality to be the last premise. *)
  val rev_cut_eq = prove_goal IFOL.thy "[| a=b;  a=b ==> R |] ==> R"
   (fn prems => [ REPEAT(resolve_tac prems 1) ]);

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
  val sizef = size_of_thm
  val mp = mp
  val not_elim = notE
  val swap = swap
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

val FOL_dup_cs = prop_cs addSIs [allI] addIs [exCI,ex1I] 
                         addSEs [exE,ex1E] addEs [all_dupE];

use "simpdata.ML";

use "../Pure/install_pp.ML";
print_depth 8;

val FOL_build_completed = ();	(*indicate successful build*)

