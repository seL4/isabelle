(*  Title:      FOL/cladata.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996  University of Cambridge

Setting up the classical reasoner 
*)


section "Classical Reasoner";


(*** Applying ClassicalFun to create a classical prover ***)
structure Classical_Data = 
  struct
  val sizef     = size_of_thm
  val mp        = mp
  val not_elim  = notE
  val classical = classical
  val hyp_subst_tacs=[hyp_subst_tac]
  end;

structure Cla = ClassicalFun(Classical_Data);
open Cla;

(*Better for fast_tac: needs no quantifier duplication!*)
qed_goal "alt_ex1E" IFOL.thy
    "[| EX! x. P(x);                                              \
\       !!x. [| P(x);  ALL y y'. P(y) & P(y') --> y=y' |] ==> R  \
\    |] ==> R"
 (fn major::prems =>
  [ (rtac (major RS ex1E) 1),
    (REPEAT (ares_tac (allI::prems) 1)),
    (etac (dup_elim allE) 1),
    (IntPr.fast_tac 1)]);


(*Propositional rules*)
val prop_cs = empty_cs addSIs [refl,TrueI,conjI,disjCI,impI,notI,iffI] 
                       addSEs [conjE,disjE,impCE,FalseE,iffCE];

(*Quantifier rules*)
val FOL_cs = prop_cs addSIs [allI,ex_ex1I] addIs [exI] 
                     addSEs [exE,alt_ex1E] addEs [allE];

claset_ref() := FOL_cs;


(*** Applying BlastFun to create Blast_tac ***)
structure Blast_Data = 
  struct
  type claset	= Cla.claset
  val notE	= notE
  val ccontr	= ccontr
  val contr_tac = Cla.contr_tac
  val dup_intr	= Cla.dup_intr
  val hyp_subst_tac = Hypsubst.blast_hyp_subst_tac
  val claset	= Cla.claset
  val rep_cs    = Cla.rep_cs
  end;

structure Blast = BlastFun(Blast_Data);

val Blast_tac = Blast.Blast_tac
and blast_tac = Blast.blast_tac;


