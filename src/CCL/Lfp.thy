(*  Title:      CCL/Lfp.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

section {* The Knaster-Tarski Theorem *}

theory Lfp
imports Set
begin

definition
  lfp :: "['a set\<Rightarrow>'a set] \<Rightarrow> 'a set" where -- "least fixed point"
  "lfp(f) == Inter({u. f(u) <= u})"

(* lfp(f) is the greatest lower bound of {u. f(u) <= u} *)

lemma lfp_lowerbound: "f(A) <= A \<Longrightarrow> lfp(f) <= A"
  unfolding lfp_def by blast

lemma lfp_greatest: "(\<And>u. f(u) <= u \<Longrightarrow> A<=u) \<Longrightarrow> A <= lfp(f)"
  unfolding lfp_def by blast

lemma lfp_lemma2: "mono(f) \<Longrightarrow> f(lfp(f)) <= lfp(f)"
  by (rule lfp_greatest, rule subset_trans, drule monoD, rule lfp_lowerbound, assumption+)

lemma lfp_lemma3: "mono(f) \<Longrightarrow> lfp(f) <= f(lfp(f))"
  by (rule lfp_lowerbound, frule monoD, drule lfp_lemma2, assumption+)

lemma lfp_Tarski: "mono(f) \<Longrightarrow> lfp(f) = f(lfp(f))"
  by (rule equalityI lfp_lemma2 lfp_lemma3 | assumption)+


(*** General induction rule for least fixed points ***)

lemma induct:
  assumes lfp: "a: lfp(f)"
    and mono: "mono(f)"
    and indhyp: "\<And>x. \<lbrakk>x: f(lfp(f) Int {x. P(x)})\<rbrakk> \<Longrightarrow> P(x)"
  shows "P(a)"
  apply (rule_tac a = a in Int_lower2 [THEN subsetD, THEN CollectD])
  apply (rule lfp [THEN [2] lfp_lowerbound [THEN subsetD]])
  apply (rule Int_greatest, rule subset_trans, rule Int_lower1 [THEN mono [THEN monoD]],
    rule mono [THEN lfp_lemma2], rule CollectI [THEN subsetI], rule indhyp, assumption)
  done

(** Definition forms of lfp_Tarski and induct, to control unfolding **)

lemma def_lfp_Tarski: "\<lbrakk>h == lfp(f); mono(f)\<rbrakk> \<Longrightarrow> h = f(h)"
  apply unfold
  apply (drule lfp_Tarski)
  apply assumption
  done

lemma def_induct: "\<lbrakk>A == lfp(f);  a:A;  mono(f); \<And>x. x: f(A Int {x. P(x)}) \<Longrightarrow> P(x)\<rbrakk> \<Longrightarrow> P(a)"
  apply (rule induct [of concl: P a])
    apply simp
   apply assumption
  apply blast
  done

(*Monotonicity of lfp!*)
lemma lfp_mono: "\<lbrakk>mono(g); \<And>Z. f(Z) <= g(Z)\<rbrakk> \<Longrightarrow> lfp(f) <= lfp(g)"
  apply (rule lfp_lowerbound)
  apply (rule subset_trans)
   apply (erule meta_spec)
  apply (erule lfp_lemma2)
  done

end
