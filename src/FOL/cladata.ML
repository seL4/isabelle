(*  Title:      FOL/cladata.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996  University of Cambridge

Setting up the classical reasoner.
*)

section "Classical Reasoner";

(*** Applying Make_Elim_Fun to create a classical "make_elim" rule ***)
structure Make_Elim = Make_Elim_Fun(val classical = classical);

(*we don't redeclare the original make_elim (Tactic.make_elim) for 
  compatibliity with strange things done in many existing proofs *)
val cla_make_elim = Make_Elim.make_elim;

(*** Applying ClassicalFun to create a classical prover ***)
structure Classical_Data = 
  struct
  val make_elim = cla_make_elim
  val mp        = mp
  val not_elim  = notE
  val classical = classical
  val sizef     = size_of_thm
  val hyp_subst_tacs=[hyp_subst_tac]
  end;

structure Cla = ClassicalFun(Classical_Data);
structure BasicClassical: BASIC_CLASSICAL = Cla; open BasicClassical;


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

val clasetup = [fn thy => (claset_ref_of thy := FOL_cs; thy)];
