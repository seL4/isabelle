(*  Title:      HOL/cladata.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996  University of Cambridge

Setting up the classical reasoner 
*)


(** Applying HypsubstFun to generate hyp_subst_tac **)
section "Classical Reasoner";

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
  val sizef     = size_of_thm
  val mp        = mp
  val not_elim  = notE
  val classical = classical
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

exception CS_DATA of claset;

let fun merge [] = CS_DATA empty_cs
      | merge cs = let val cs = map (fn CS_DATA x => x) cs;
                   in CS_DATA (foldl merge_cs (hd cs, tl cs)) end;

    fun put (CS_DATA cs) = claset := cs;

    fun get () = CS_DATA (!claset);
in add_thydata "HOL"
     ("claset", ThyMethods {merge = merge, put = put, get = get})
end;

claset := HOL_cs;


(*** Applying BlastFun to create Blast_tac ***)
structure Blast_Data = 
  struct
  type claset	= Classical.claset
  val notE	= notE
  val ccontr	= ccontr
  val contr_tac = Classical.contr_tac
  val dup_intr	= Classical.dup_intr
  val vars_gen_hyp_subst_tac = Hypsubst.vars_gen_hyp_subst_tac
  val claset	= Classical.claset
  val rep_claset = Classical.rep_claset
  end;

structure Blast = BlastFun(Blast_Data);
Blast.declConsts (["op ="], [iffI]);	(*overloading of equality as iff*)

val Blast_tac = Blast.Blast_tac
and blast_tac = Blast.blast_tac;
