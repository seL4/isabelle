(*  Title:      HOL/ROOT.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1993  University of Cambridge

Adds Classical Higher-order Logic to a database containing Pure Isabelle.
Should be executed in the subdirectory HOL.
*)

val banner = "Higher-Order Logic with curried functions";
writeln banner;

print_depth 1;
set eta_contract;

(* Add user sections *)
use "../Pure/section_utils.ML";
use "thy_syntax.ML";

use_thy "HOL";
use "../Provers/splitter.ML";
use "../Provers/hypsubst.ML";
use "../Provers/classical.ML";

(** Applying HypsubstFun to generate hyp_subst_tac **)

structure Hypsubst_Data =
  struct
  structure Simplifier = Simplifier
  (*Take apart an equality judgement; otherwise raise Match!*)
  fun dest_eq (Const("Trueprop",_) $ (Const("op =",_)  $ t $ u)) = (t,u);
  val eq_reflection = eq_reflection
  val imp_intr = impI
  val rev_mp = rev_mp
  val subst = subst
  val sym = sym
  end;

structure Hypsubst = HypsubstFun(Hypsubst_Data);
open Hypsubst;

(*** Applying ClassicalFun to create a classical prover ***)
structure Classical_Data = 
  struct
  val sizef	= size_of_thm
  val mp	= mp
  val not_elim	= notE
  val classical	= classical
  val hyp_subst_tacs=[hyp_subst_tac]
  end;

structure Classical = ClassicalFun(Classical_Data);
open Classical;

(*Propositional rules*)
val prop_cs = empty_cs addSIs [refl,TrueI,conjI,disjCI,impI,notI,iffI]
                       addSEs [conjE,disjE,impCE,FalseE,iffE];

(*Quantifier rules*)
val HOL_cs = prop_cs addSIs [allI] addIs [exI,ex1I]
                     addSEs [exE,ex1E] addEs [allE];

use     "simpdata.ML";
use_thy "Ord";
use_thy "subset";
use     "hologic.ML";
use     "subtype.ML";
use_thy "Prod";
use_thy "Sum";
use_thy "Gfp";
use_thy "Nat";

use "datatype.ML";
use "ind_syntax.ML";
use "add_ind_def.ML";
use "intr_elim.ML";
use "indrule.ML";
use_thy "Inductive";

use_thy "Finite";
use_thy "Sexp";
use_thy "List";

init_pps ();
print_depth 8;

val HOL_build_completed = ();   (*indicate successful build*)
