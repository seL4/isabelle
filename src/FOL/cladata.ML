(*  Title:      FOL/cladata.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996  University of Cambridge

Setting up the classical reasoner 
*)


(** Applying HypsubstFun to generate hyp_subst_tac **)
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
    "[| EX! x.P(x);                                              \
\       !!x. [| P(x);  ALL y y'. P(y) & P(y') --> y=y' |] ==> R  \
\    |] ==> R"
 (fn major::prems =>
  [ (rtac (major RS ex1E) 1),
    (REPEAT (ares_tac (allI::prems) 1)),
    (etac (dup_elim allE) 1),
    (IntPr.fast_tac 1)]);


(*Propositional rules 
  -- iffCE might seem better, but in the examples in ex/cla
     run about 7% slower than with iffE*)
val prop_cs = empty_cs addSIs [refl,TrueI,conjI,disjCI,impI,notI,iffI] 
                       addSEs [conjE,disjE,impCE,FalseE,iffE];

(*Quantifier rules*)
val FOL_cs = prop_cs addSIs [allI,ex_ex1I] addIs [exI] 
                     addSEs [exE,alt_ex1E] addEs [allE];


exception CS_DATA of claset;

let fun merge [] = CS_DATA empty_cs
      | merge cs = let val cs = map (fn CS_DATA x => x) cs;
                   in CS_DATA (foldl merge_cs (hd cs, tl cs)) end;

    fun put (CS_DATA cs) = claset := cs;

    fun get () = CS_DATA (!claset);
in add_thydata "FOL"
     ("claset", ThyMethods {merge = merge, put = put, get = get})
end;

claset := FOL_cs;

