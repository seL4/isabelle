(*  Title:      HOL/Lfp.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

The Knaster-Tarski Theorem.
*)

(*** Proof of Knaster-Tarski Theorem ***)

(* lfp(f) is the greatest lower bound of {u. f(u) <= u} *)

Goalw [lfp_def] "f(A) <= A ==> lfp(f) <= A";
by (rtac (CollectI RS Inter_lower) 1);
by (assume_tac 1);
qed "lfp_lowerbound";

val prems = Goalw [lfp_def]
    "[| !!u. f(u) <= u ==> A<=u |] ==> A <= lfp(f)";
by (REPEAT (ares_tac ([Inter_greatest]@prems) 1));
by (etac CollectD 1);
qed "lfp_greatest";

Goal "mono(f) ==> f(lfp(f)) <= lfp(f)";
by (EVERY1 [rtac lfp_greatest, rtac subset_trans,
            etac monoD, rtac lfp_lowerbound, atac, atac]);
qed "lfp_lemma2";

Goal "mono(f) ==> lfp(f) <= f(lfp(f))";
by (EVERY1 [rtac lfp_lowerbound, rtac monoD, assume_tac,
            etac lfp_lemma2]);
qed "lfp_lemma3";

Goal "mono(f) ==> lfp(f) = f(lfp(f))";
by (REPEAT (ares_tac [equalityI,lfp_lemma2,lfp_lemma3] 1));
qed "lfp_Tarski";

(*** General induction rule for least fixed points ***)

val [lfp,mono,indhyp] = Goal
    "[| a: lfp(f);  mono(f);                            \
\       !!x. [| x: f(lfp(f) Int {x. P(x)}) |] ==> P(x)   \
\    |] ==> P(a)";
by (res_inst_tac [("a","a")] (Int_lower2 RS subsetD RS CollectD) 1);
by (rtac (lfp RSN (2, lfp_lowerbound RS subsetD)) 1);
by (EVERY1 [rtac Int_greatest, rtac subset_trans, 
            rtac (Int_lower1 RS (mono RS monoD)),
            rtac (mono RS lfp_lemma2),
            rtac (CollectI RS subsetI), rtac indhyp, atac]);
qed "induct";

bind_thm ("induct2",
  split_rule (read_instantiate [("a","(a,b)")] induct));


(** Definition forms of lfp_Tarski and induct, to control unfolding **)

val [rew,mono] = goal (the_context ()) "[| h==lfp(f);  mono(f) |] ==> h = f(h)";
by (rewtac rew);
by (rtac (mono RS lfp_Tarski) 1);
qed "def_lfp_Tarski";

val rew::prems = Goal
    "[| A == lfp(f);  mono(f);   a:A;                   \
\       !!x. [| x: f(A Int {x. P(x)}) |] ==> P(x)        \
\    |] ==> P(a)";
by (EVERY1 [rtac induct,        (*backtracking to force correct induction*)
            REPEAT1 o (ares_tac (map (rewrite_rule [rew]) prems))]);
qed "def_induct";

(*Monotonicity of lfp!*)
val [prem] = Goal "[| !!Z. f(Z)<=g(Z) |] ==> lfp(f) <= lfp(g)";
by (rtac (lfp_lowerbound RS lfp_greatest) 1);
by (etac (prem RS subset_trans) 1);
qed "lfp_mono";
