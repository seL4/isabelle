(*  Title:      Sequents/LK.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Axiom to express monotonicity (a variant of the deduction theorem).  Makes the
link between \<turnstile> and \<Longrightarrow>, needed for instance to prove imp_cong.

Axiom left_cong allows the simplifier to use left-side formulas.  Ideally it
should be derived from lower-level axioms.

CANNOT be added to LK0.thy because modal logic is built upon it, and
various modal rules would become inconsistent.
*)

theory LK
imports LK0
begin

axiomatization where
  monotonic:  "($H \<turnstile> P \<Longrightarrow> $H \<turnstile> Q) \<Longrightarrow> $H, P \<turnstile> Q" and

  left_cong:  "\<lbrakk>P == P';  \<turnstile> P' \<Longrightarrow> ($H \<turnstile> $F) \<equiv> ($H' \<turnstile> $F')\<rbrakk>
               \<Longrightarrow> (P, $H \<turnstile> $F) \<equiv> (P', $H' \<turnstile> $F')"


subsection \<open>Rewrite rules\<close>

lemma conj_simps:
  "\<turnstile> P \<and> True \<longleftrightarrow> P"
  "\<turnstile> True \<and> P \<longleftrightarrow> P"
  "\<turnstile> P \<and> False \<longleftrightarrow> False"
  "\<turnstile> False \<and> P \<longleftrightarrow> False"
  "\<turnstile> P \<and> P \<longleftrightarrow> P"
  "\<turnstile> P \<and> P \<and> Q \<longleftrightarrow> P \<and> Q"
  "\<turnstile> P \<and> \<not> P \<longleftrightarrow> False"
  "\<turnstile> \<not> P \<and> P \<longleftrightarrow> False"
  "\<turnstile> (P \<and> Q) \<and> R \<longleftrightarrow> P \<and> (Q \<and> R)"
  by (fast add!: subst)+

lemma disj_simps:
  "\<turnstile> P \<or> True \<longleftrightarrow> True"
  "\<turnstile> True \<or> P \<longleftrightarrow> True"
  "\<turnstile> P \<or> False \<longleftrightarrow> P"
  "\<turnstile> False \<or> P \<longleftrightarrow> P"
  "\<turnstile> P \<or> P \<longleftrightarrow> P"
  "\<turnstile> P \<or> P \<or> Q \<longleftrightarrow> P \<or> Q"
  "\<turnstile> (P \<or> Q) \<or> R \<longleftrightarrow> P \<or> (Q \<or> R)"
  by (fast add!: subst)+

lemma not_simps:
  "\<turnstile> \<not> False \<longleftrightarrow> True"
  "\<turnstile> \<not> True \<longleftrightarrow> False"
  by (fast add!: subst)+

lemma imp_simps:
  "\<turnstile> (P \<longrightarrow> False) \<longleftrightarrow> \<not> P"
  "\<turnstile> (P \<longrightarrow> True) \<longleftrightarrow> True"
  "\<turnstile> (False \<longrightarrow> P) \<longleftrightarrow> True"
  "\<turnstile> (True \<longrightarrow> P) \<longleftrightarrow> P"
  "\<turnstile> (P \<longrightarrow> P) \<longleftrightarrow> True"
  "\<turnstile> (P \<longrightarrow> \<not> P) \<longleftrightarrow> \<not> P"
  by (fast add!: subst)+

lemma iff_simps:
  "\<turnstile> (True \<longleftrightarrow> P) \<longleftrightarrow> P"
  "\<turnstile> (P \<longleftrightarrow> True) \<longleftrightarrow> P"
  "\<turnstile> (P \<longleftrightarrow> P) \<longleftrightarrow> True"
  "\<turnstile> (False \<longleftrightarrow> P) \<longleftrightarrow> \<not> P"
  "\<turnstile> (P \<longleftrightarrow> False) \<longleftrightarrow> \<not> P"
  by (fast add!: subst)+

lemma quant_simps:
  "\<And>P. \<turnstile> (\<forall>x. P) \<longleftrightarrow> P"
  "\<And>P. \<turnstile> (\<forall>x. x = t \<longrightarrow> P(x)) \<longleftrightarrow> P(t)"
  "\<And>P. \<turnstile> (\<forall>x. t = x \<longrightarrow> P(x)) \<longleftrightarrow> P(t)"
  "\<And>P. \<turnstile> (\<exists>x. P) \<longleftrightarrow> P"
  "\<And>P. \<turnstile> (\<exists>x. x = t \<and> P(x)) \<longleftrightarrow> P(t)"
  "\<And>P. \<turnstile> (\<exists>x. t = x \<and> P(x)) \<longleftrightarrow> P(t)"
  by (fast add!: subst)+


subsection \<open>Miniscoping: pushing quantifiers in\<close>

text \<open>
  We do NOT distribute of \<forall> over \<and>, or dually that of \<exists> over \<or>
  Baaz and Leitsch, On Skolemization and Proof Complexity (1994)
  show that this step can increase proof length!
\<close>

text \<open>existential miniscoping\<close>
lemma ex_simps:
  "\<And>P Q. \<turnstile> (\<exists>x. P(x) \<and> Q) \<longleftrightarrow> (\<exists>x. P(x)) \<and> Q"
  "\<And>P Q. \<turnstile> (\<exists>x. P \<and> Q(x)) \<longleftrightarrow> P \<and> (\<exists>x. Q(x))"
  "\<And>P Q. \<turnstile> (\<exists>x. P(x) \<or> Q) \<longleftrightarrow> (\<exists>x. P(x)) \<or> Q"
  "\<And>P Q. \<turnstile> (\<exists>x. P \<or> Q(x)) \<longleftrightarrow> P \<or> (\<exists>x. Q(x))"
  "\<And>P Q. \<turnstile> (\<exists>x. P(x) \<longrightarrow> Q) \<longleftrightarrow> (\<forall>x. P(x)) \<longrightarrow> Q"
  "\<And>P Q. \<turnstile> (\<exists>x. P \<longrightarrow> Q(x)) \<longleftrightarrow> P \<longrightarrow> (\<exists>x. Q(x))"
  by (fast add!: subst)+

text \<open>universal miniscoping\<close>
lemma all_simps:
  "\<And>P Q. \<turnstile> (\<forall>x. P(x) \<and> Q) \<longleftrightarrow> (\<forall>x. P(x)) \<and> Q"
  "\<And>P Q. \<turnstile> (\<forall>x. P \<and> Q(x)) \<longleftrightarrow> P \<and> (\<forall>x. Q(x))"
  "\<And>P Q. \<turnstile> (\<forall>x. P(x) \<longrightarrow> Q) \<longleftrightarrow> (\<exists>x. P(x)) \<longrightarrow> Q"
  "\<And>P Q. \<turnstile> (\<forall>x. P \<longrightarrow> Q(x)) \<longleftrightarrow> P \<longrightarrow> (\<forall>x. Q(x))"
  "\<And>P Q. \<turnstile> (\<forall>x. P(x) \<or> Q) \<longleftrightarrow> (\<forall>x. P(x)) \<or> Q"
  "\<And>P Q. \<turnstile> (\<forall>x. P \<or> Q(x)) \<longleftrightarrow> P \<or> (\<forall>x. Q(x))"
  by (fast add!: subst)+

text \<open>These are NOT supplied by default!\<close>
lemma distrib_simps:
  "\<turnstile> P \<and> (Q \<or> R) \<longleftrightarrow> P \<and> Q \<or> P \<and> R"
  "\<turnstile> (Q \<or> R) \<and> P \<longleftrightarrow> Q \<and> P \<or> R \<and> P"
  "\<turnstile> (P \<or> Q \<longrightarrow> R) \<longleftrightarrow> (P \<longrightarrow> R) \<and> (Q \<longrightarrow> R)"
  by (fast add!: subst)+

lemma P_iff_F: "\<turnstile> \<not> P \<Longrightarrow> \<turnstile> (P \<longleftrightarrow> False)"
  apply (erule thinR [THEN cut])
  apply fast
  done

lemmas iff_reflection_F = P_iff_F [THEN iff_reflection]

lemma P_iff_T: "\<turnstile> P \<Longrightarrow> \<turnstile> (P \<longleftrightarrow> True)"
  apply (erule thinR [THEN cut])
  apply fast
  done

lemmas iff_reflection_T = P_iff_T [THEN iff_reflection]


lemma LK_extra_simps:
  "\<turnstile> P \<or> \<not> P"
  "\<turnstile> \<not> P \<or> P"
  "\<turnstile> \<not> \<not> P \<longleftrightarrow> P"
  "\<turnstile> (\<not> P \<longrightarrow> P) \<longleftrightarrow> P"
  "\<turnstile> (\<not> P \<longleftrightarrow> \<not> Q) \<longleftrightarrow> (P \<longleftrightarrow> Q)"
  by (fast add!: subst)+


subsection \<open>Named rewrite rules\<close>

lemma conj_commute: "\<turnstile> P \<and> Q \<longleftrightarrow> Q \<and> P"
  and conj_left_commute: "\<turnstile> P \<and> (Q \<and> R) \<longleftrightarrow> Q \<and> (P \<and> R)"
  by (fast add!: subst)+

lemmas conj_comms = conj_commute conj_left_commute

lemma disj_commute: "\<turnstile> P \<or> Q \<longleftrightarrow> Q \<or> P"
  and disj_left_commute: "\<turnstile> P \<or> (Q \<or> R) \<longleftrightarrow> Q \<or> (P \<or> R)"
  by (fast add!: subst)+

lemmas disj_comms = disj_commute disj_left_commute

lemma conj_disj_distribL: "\<turnstile> P \<and> (Q \<or> R) \<longleftrightarrow> (P \<and> Q \<or> P \<and> R)"
  and conj_disj_distribR: "\<turnstile> (P \<or> Q) \<and> R \<longleftrightarrow> (P \<and> R \<or> Q \<and> R)"

  and disj_conj_distribL: "\<turnstile> P \<or> (Q \<and> R) \<longleftrightarrow> (P \<or> Q) \<and> (P \<or> R)"
  and disj_conj_distribR: "\<turnstile> (P \<and> Q) \<or> R \<longleftrightarrow> (P \<or> R) \<and> (Q \<or> R)"

  and imp_conj_distrib: "\<turnstile> (P \<longrightarrow> (Q \<and> R)) \<longleftrightarrow> (P \<longrightarrow> Q) \<and> (P \<longrightarrow> R)"
  and imp_conj: "\<turnstile> ((P \<and> Q) \<longrightarrow> R)  \<longleftrightarrow> (P \<longrightarrow> (Q \<longrightarrow> R))"
  and imp_disj: "\<turnstile> (P \<or> Q \<longrightarrow> R)  \<longleftrightarrow> (P \<longrightarrow> R) \<and> (Q \<longrightarrow> R)"

  and imp_disj1: "\<turnstile> (P \<longrightarrow> Q) \<or> R \<longleftrightarrow> (P \<longrightarrow> Q \<or> R)"
  and imp_disj2: "\<turnstile> Q \<or> (P \<longrightarrow> R) \<longleftrightarrow> (P \<longrightarrow> Q \<or> R)"

  and de_Morgan_disj: "\<turnstile> (\<not> (P \<or> Q)) \<longleftrightarrow> (\<not> P \<and> \<not> Q)"
  and de_Morgan_conj: "\<turnstile> (\<not> (P \<and> Q)) \<longleftrightarrow> (\<not> P \<or> \<not> Q)"

  and not_iff: "\<turnstile> \<not> (P \<longleftrightarrow> Q) \<longleftrightarrow> (P \<longleftrightarrow> \<not> Q)"
  by (fast add!: subst)+

lemma imp_cong:
  assumes p1: "\<turnstile> P \<longleftrightarrow> P'"
    and p2: "\<turnstile> P' \<Longrightarrow> \<turnstile> Q \<longleftrightarrow> Q'"
  shows "\<turnstile> (P \<longrightarrow> Q) \<longleftrightarrow> (P' \<longrightarrow> Q')"
  apply (lem p1)
  apply safe
   apply (tactic \<open>
     REPEAT (resolve_tac \<^context> @{thms cut} 1 THEN
       DEPTH_SOLVE_1
         (resolve_tac \<^context> [@{thm thinL}, @{thm thinR}, @{thm p2} COMP @{thm monotonic}] 1) THEN
           Cla.safe_tac \<^context> 1)\<close>)
  done

lemma conj_cong:
  assumes p1: "\<turnstile> P \<longleftrightarrow> P'"
    and p2: "\<turnstile> P' \<Longrightarrow> \<turnstile> Q \<longleftrightarrow> Q'"
  shows "\<turnstile> (P \<and> Q) \<longleftrightarrow> (P' \<and> Q')"
  apply (lem p1)
  apply safe
   apply (tactic \<open>
     REPEAT (resolve_tac \<^context> @{thms cut} 1 THEN
       DEPTH_SOLVE_1
         (resolve_tac \<^context> [@{thm thinL}, @{thm thinR}, @{thm p2} COMP @{thm monotonic}] 1) THEN
           Cla.safe_tac \<^context> 1)\<close>)
  done

lemma eq_sym_conv: "\<turnstile> x = y \<longleftrightarrow> y = x"
  by (fast add!: subst)

ML_file \<open>simpdata.ML\<close>
setup \<open>Simplifier.map_theory_simpset (put_simpset LK_ss)\<close>
setup \<open>Simplifier.method_setup []\<close>


text \<open>To create substitution rules\<close>

lemma eq_imp_subst: "\<turnstile> a = b \<Longrightarrow> $H, A(a), $G \<turnstile> $E, A(b), $F"
  by simp

lemma split_if: "\<turnstile> P(if Q then x else y) \<longleftrightarrow> ((Q \<longrightarrow> P(x)) \<and> (\<not> Q \<longrightarrow> P(y)))"
  apply (rule_tac P = Q in cut)
   prefer 2
   apply (simp add: if_P)
  apply (rule_tac P = "\<not> Q" in cut)
   prefer 2
   apply (simp add: if_not_P)
  apply fast
  done

lemma if_cancel: "\<turnstile> (if P then x else x) = x"
  apply (lem split_if)
  apply fast
  done

lemma if_eq_cancel: "\<turnstile> (if x = y then y else x) = x"
  apply (lem split_if)
  apply safe
  apply (rule symL)
  apply (rule basic)
  done

end
