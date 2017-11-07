(* Author: Tobias Nipkow *)

subsection \<open>Soundness and Completeness\<close>

theory Hoare_Sound_Complete
imports Hoare
begin

subsubsection "Soundness"

lemma hoare_sound: "\<turnstile> {P}c{Q}  \<Longrightarrow>  \<Turnstile> {P}c{Q}"
proof(induction rule: hoare.induct)
  case (While P b c)
  have "(WHILE b DO c,s) \<Rightarrow> t  \<Longrightarrow>  P s  \<Longrightarrow>  P t \<and> \<not> bval b t" for s t
  proof(induction "WHILE b DO c" s t rule: big_step_induct)
    case WhileFalse thus ?case by blast
  next
    case WhileTrue thus ?case
      using While.IH unfolding hoare_valid_def by blast
  qed
  thus ?case unfolding hoare_valid_def by blast
qed (auto simp: hoare_valid_def)


subsubsection "Weakest Precondition"

definition wp :: "com \<Rightarrow> assn \<Rightarrow> assn" where
"wp c Q = (\<lambda>s. \<forall>t. (c,s) \<Rightarrow> t  \<longrightarrow>  Q t)"

lemma wp_SKIP[simp]: "wp SKIP Q = Q"
by (rule ext) (auto simp: wp_def)

lemma wp_Ass[simp]: "wp (x::=a) Q = (\<lambda>s. Q(s[a/x]))"
by (rule ext) (auto simp: wp_def)

lemma wp_Seq[simp]: "wp (c\<^sub>1;;c\<^sub>2) Q = wp c\<^sub>1 (wp c\<^sub>2 Q)"
by (rule ext) (auto simp: wp_def)

lemma wp_If[simp]:
 "wp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q =
 (\<lambda>s. if bval b s then wp c\<^sub>1 Q s else wp c\<^sub>2 Q s)"
by (rule ext) (auto simp: wp_def)

lemma wp_While_If:
 "wp (WHILE b DO c) Q s =
  wp (IF b THEN c;;WHILE b DO c ELSE SKIP) Q s"
unfolding wp_def by (metis unfold_while)

lemma wp_While_True[simp]: "bval b s \<Longrightarrow>
  wp (WHILE b DO c) Q s = wp (c;; WHILE b DO c) Q s"
by(simp add: wp_While_If)

lemma wp_While_False[simp]: "\<not> bval b s \<Longrightarrow> wp (WHILE b DO c) Q s = Q s"
by(simp add: wp_While_If)


subsubsection "Completeness"

lemma wp_is_pre: "\<turnstile> {wp c Q} c {Q}"
proof(induction c arbitrary: Q)
  case If thus ?case by(auto intro: conseq)
next
  case (While b c)
  let ?w = "WHILE b DO c"
  show "\<turnstile> {wp ?w Q} ?w {Q}"
  proof(rule While')
    show "\<turnstile> {\<lambda>s. wp ?w Q s \<and> bval b s} c {wp ?w Q}"
    proof(rule strengthen_pre[OF _ While.IH])
      show "\<forall>s. wp ?w Q s \<and> bval b s \<longrightarrow> wp c (wp ?w Q) s" by auto
    qed
    show "\<forall>s. wp ?w Q s \<and> \<not> bval b s \<longrightarrow> Q s" by auto
  qed
qed auto

lemma hoare_complete: assumes "\<Turnstile> {P}c{Q}" shows "\<turnstile> {P}c{Q}"
proof(rule strengthen_pre)
  show "\<forall>s. P s \<longrightarrow> wp c Q s" using assms
    by (auto simp: hoare_valid_def wp_def)
  show "\<turnstile> {wp c Q} c {Q}" by(rule wp_is_pre)
qed

corollary hoare_sound_complete: "\<turnstile> {P}c{Q} \<longleftrightarrow> \<Turnstile> {P}c{Q}"
by (metis hoare_complete hoare_sound)

end
