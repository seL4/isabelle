(*  Title:      HOL/Lfp.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

The Knaster-Tarski Theorem.
*)

(*** Proof of Knaster-Tarski Theorem ***)

val lfp_def = thm "lfp_def";

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
qed "lfp_unfold";

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
qed "lfp_induct";

bind_thm ("lfp_induct2",
  split_rule (read_instantiate [("a","(a,b)")] lfp_induct));


val major::prems = Goal
 "[| mono f; !!S. P S ==> P(f S); !!M. !S:M. P S ==> P(Union M) |] ==> \
\ P(lfp f)";
by(subgoal_tac "lfp f = Union{S. S <= lfp f & P S}" 1);
 by(etac ssubst 1);
 by(simp_tac (simpset() addsimps prems) 1);
by(subgoal_tac "Union{S. S <= lfp f & P S} <= lfp f" 1);
 by(Blast_tac 2);
by(rtac equalityI 1);
 by(atac 2);
by(dtac (major RS monoD) 1);
by(cut_facts_tac [major RS lfp_unfold] 1);
by(Asm_full_simp_tac 1);
by(rtac lfp_lowerbound 1);
by(blast_tac (claset() addSIs prems) 1);
qed "lfp_ordinal_induct";


(** Definition forms of lfp_unfold and lfp_induct, to control unfolding **)

Goal "[| h==lfp(f);  mono(f) |] ==> h = f(h)";
by (auto_tac (claset() addSIs [lfp_unfold], simpset()));  
qed "def_lfp_unfold";

val rew::prems = Goal
    "[| A == lfp(f);  mono(f);   a:A;                   \
\       !!x. [| x: f(A Int {x. P(x)}) |] ==> P(x)        \
\    |] ==> P(a)";
by (EVERY1 [rtac lfp_induct,        (*backtracking to force correct induction*)
            REPEAT1 o (ares_tac (map (rewrite_rule [rew]) prems))]);
qed "def_lfp_induct";

(*Monotonicity of lfp!*)
val [prem] = Goal "[| !!Z. f(Z)<=g(Z) |] ==> lfp(f) <= lfp(g)";
by (rtac (lfp_lowerbound RS lfp_greatest) 1);
by (etac (prem RS subset_trans) 1);
qed "lfp_mono";
