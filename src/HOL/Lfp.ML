(*  Title: 	HOL/lfp.ML
    ID:         $Id$
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
qed "lfp_lowerbound";

val prems = goalw Lfp.thy [lfp_def]
    "[| !!u. f(u) <= u ==> A<=u |] ==> A <= lfp(f)";
by (REPEAT (ares_tac ([Inter_greatest]@prems) 1));
by (etac CollectD 1);
qed "lfp_greatest";

val [mono] = goal Lfp.thy "mono(f) ==> f(lfp(f)) <= lfp(f)";
by (EVERY1 [rtac lfp_greatest, rtac subset_trans,
	    rtac (mono RS monoD), rtac lfp_lowerbound, atac, atac]);
qed "lfp_lemma2";

val [mono] = goal Lfp.thy "mono(f) ==> lfp(f) <= f(lfp(f))";
by (EVERY1 [rtac lfp_lowerbound, rtac (mono RS monoD), 
	    rtac lfp_lemma2, rtac mono]);
qed "lfp_lemma3";

val [mono] = goal Lfp.thy "mono(f) ==> lfp(f) = f(lfp(f))";
by (REPEAT (resolve_tac [equalityI,lfp_lemma2,lfp_lemma3,mono] 1));
qed "lfp_Tarski";

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
qed "induct";

val major::prems = goal Lfp.thy
  "[| (a,b) : lfp f; mono f; \
\     !!a b. (a,b) : f(lfp f Int Collect(split P)) ==> P a b |] ==> P a b";
by(res_inst_tac [("c1","P")] (split RS subst) 1);
br (major RS induct) 1;
brs prems 1;
by(res_inst_tac[("p","x")]PairE 1);
by(hyp_subst_tac 1);
by(asm_simp_tac (!simpset addsimps prems) 1);
qed"induct2";

(*** Fixpoint induction a la David Park ***)
goal Lfp.thy "!!f. [| mono f; f A <= A |] ==> lfp(f) <= A";
br subsetI 1;
by(EVERY[etac induct 1, atac 1, etac subsetD 1, rtac subsetD 1,
                atac 2, fast_tac (set_cs addSEs [monoD]) 1]);
qed "Park_induct";

(** Definition forms of lfp_Tarski and induct, to control unfolding **)

val [rew,mono] = goal Lfp.thy "[| h==lfp(f);  mono(f) |] ==> h = f(h)";
by (rewtac rew);
by (rtac (mono RS lfp_Tarski) 1);
qed "def_lfp_Tarski";

val rew::prems = goal Lfp.thy
    "[| A == lfp(f);  mono(f);   a:A;  			\
\       !!x. [| x: f(A Int {x.P(x)}) |] ==> P(x) 	\
\    |] ==> P(a)";
by (EVERY1 [rtac induct,	(*backtracking to force correct induction*)
	    REPEAT1 o (ares_tac (map (rewrite_rule [rew]) prems))]);
qed "def_induct";

(*Monotonicity of lfp!*)
val [prem] = goal Lfp.thy "[| !!Z. f(Z)<=g(Z) |] ==> lfp(f) <= lfp(g)";
br (lfp_lowerbound RS lfp_greatest) 1;
be (prem RS subset_trans) 1;
qed "lfp_mono";
