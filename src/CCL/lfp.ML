(*  Title: 	CCL/lfp
    ID:         $Id$

Modified version of
    Title: 	HOL/lfp.ML
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

For lfp.thy.  The Knaster-Tarski Theorem
*)

open Lfp;

(*** Proof of Knaster-Tarski Theorem ***)

(* lfp(f) is the greatest lower bound of {u. f(u) <= u} *)

val prems = goalw Lfp.thy [lfp_def] "[| f(A) <= A |] ==> lfp(f) <= A";
by (rtac (CollectI RS Inter_lower) 1);
by (resolve_tac prems 1);
val lfp_lowerbound = result();

val prems = goalw Lfp.thy [lfp_def]
    "[| !!u. f(u) <= u ==> A<=u |] ==> A <= lfp(f)";
by (REPEAT (ares_tac ([Inter_greatest]@prems) 1));
by (etac CollectD 1);
val lfp_greatest = result();

val [mono] = goal Lfp.thy "mono(f) ==> f(lfp(f)) <= lfp(f)";
by (EVERY1 [rtac lfp_greatest, rtac subset_trans,
	    rtac (mono RS monoD), rtac lfp_lowerbound, atac, atac]);
val lfp_lemma2 = result();

val [mono] = goal Lfp.thy "mono(f) ==> lfp(f) <= f(lfp(f))";
by (EVERY1 [rtac lfp_lowerbound, rtac (mono RS monoD), 
	    rtac lfp_lemma2, rtac mono]);
val lfp_lemma3 = result();

val [mono] = goal Lfp.thy "mono(f) ==> lfp(f) = f(lfp(f))";
by (REPEAT (resolve_tac [equalityI,lfp_lemma2,lfp_lemma3,mono] 1));
val lfp_Tarski = result();


(*** General induction rule for least fixed points ***)

val [lfp,mono,indhyp] = goal Lfp.thy
    "[| a: lfp(f);  mono(f);  				\
\       !!x. [| x: f(lfp(f) Int {x.P(x)}) |] ==> P(x) 	\
\    |] ==> P(a)";
by (res_inst_tac [("a","a")] (Int_lower2 RS subsetD RS CollectD) 1);
by (rtac (lfp RSN (2, lfp_lowerbound RS subsetD)) 1);
by (EVERY1 [rtac Int_greatest, rtac subset_trans, 
	    rtac (Int_lower1 RS (mono RS monoD)),
	    rtac (mono RS lfp_lemma2),
	    rtac (CollectI RS subsetI), rtac indhyp, atac]);
val induct = result();

(** Definition forms of lfp_Tarski and induct, to control unfolding **)

val [rew,mono] = goal Lfp.thy "[| h==lfp(f);  mono(f) |] ==> h = f(h)";
by (rewtac rew);
by (rtac (mono RS lfp_Tarski) 1);
val def_lfp_Tarski = result();

val rew::prems = goal Lfp.thy
    "[| A == lfp(f);  a:A;  mono(f);   			\
\       !!x. [| x: f(A Int {x.P(x)}) |] ==> P(x) 	\
\    |] ==> P(a)";
by (EVERY1 [rtac induct,	(*backtracking to force correct induction*)
	    REPEAT1 o (ares_tac (map (rewrite_rule [rew]) prems))]);
val def_induct = result();

(*Monotonicity of lfp!*)
val prems = goal Lfp.thy
    "[| mono(g);  !!Z. f(Z)<=g(Z) |] ==> lfp(f) <= lfp(g)";
by (rtac lfp_lowerbound 1);
by (rtac subset_trans 1);
by (resolve_tac prems 1);
by (rtac lfp_lemma2 1);
by (resolve_tac prems 1);
val lfp_mono = result();

