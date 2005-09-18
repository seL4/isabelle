(*  Title:      FOLP/FOLP.thy
    ID:         $Id$
    Author:     Martin D Coen, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

header {* Classical First-Order Logic with Proofs *}

theory FOLP
imports IFOLP
uses
  ("FOLP_lemmas.ML") ("hypsubst.ML") ("classical.ML")
  ("simp.ML") ("intprover.ML") ("simpdata.ML")
begin

consts
  cla :: "[p=>p]=>p"
axioms
  classical: "(!!x. x:~P ==> f(x):P) ==> cla(f):P"

ML {* use_legacy_bindings (the_context ()) *}

use "FOLP_lemmas.ML"

use "hypsubst.ML"
use "classical.ML"      (* Patched 'cos matching won't instantiate proof *)
use "simp.ML"           (* Patched 'cos matching won't instantiate proof *)

ML {*

(*** Applying HypsubstFun to generate hyp_subst_tac ***)

structure Hypsubst_Data =
  struct
  (*Take apart an equality judgement; otherwise raise Match!*)
  fun dest_eq (Const("Proof",_) $ (Const("op =",_)  $ t $ u) $ _) = (t,u);

  val imp_intr = impI

  (*etac rev_cut_eq moves an equality to be the last premise. *)
  val rev_cut_eq = prove_goal (the_context ())
                "[| p:a=b;  !!x. x:a=b ==> f(x):R |] ==> ?p:R"
   (fn prems => [ REPEAT(resolve_tac prems 1) ]);

  val rev_mp = rev_mp
  val subst = subst
  val sym = sym
  val thin_refl = prove_goal (the_context ())
                  "!!X. [|p:x=x; PROP W|] ==> PROP W" (K [atac 1]);
  end;

structure Hypsubst = HypsubstFun(Hypsubst_Data);
open Hypsubst;
*}

use "intprover.ML"

ML {*
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
val FOLP_cs = prop_cs addSIs [allI] addIs [exI,ex1I]
                      addSEs [exE,ex1E] addEs [allE];

val FOLP_dup_cs = prop_cs addSIs [allI] addIs [exCI,ex1I]
                          addSEs [exE,ex1E] addEs [all_dupE];

*}

use "simpdata.ML"

end
