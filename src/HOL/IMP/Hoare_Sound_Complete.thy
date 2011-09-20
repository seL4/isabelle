(* Author: Tobias Nipkow *)

theory Hoare_Sound_Complete imports Hoare begin

subsection "Soundness"

definition
hoare_valid :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<Turnstile> {(1_)}/ (_)/ {(1_)}" 50) where
"\<Turnstile> {P}c{Q} = (\<forall>s t. (c,s) \<Rightarrow> t  \<longrightarrow>  P s \<longrightarrow>  Q t)"

lemma hoare_sound: "\<turnstile> {P}c{Q}  \<Longrightarrow>  \<Turnstile> {P}c{Q}"
proof(induction rule: hoare.induct)
  case (While P b c)
  { fix s t
    have "(WHILE b DO c,s) \<Rightarrow> t  \<Longrightarrow>  P s \<longrightarrow> P t \<and> \<not> bval b t"
    proof(induction "WHILE b DO c" s t rule: big_step_induct)
      case WhileFalse thus ?case by blast
    next
      case WhileTrue thus ?case
        using While(2) unfolding hoare_valid_def by blast
    qed
  }
  thus ?case unfolding hoare_valid_def by blast
qed (auto simp: hoare_valid_def)


subsection "Weakest Precondition"

definition wp :: "com \<Rightarrow> assn \<Rightarrow> assn" where
"wp c Q = (\<lambda>s. \<forall>t. (c,s) \<Rightarrow> t  \<longrightarrow>  Q t)"

lemma wp_SKIP[simp]: "wp SKIP Q = Q"
by (rule ext) (auto simp: wp_def)

lemma wp_Ass[simp]: "wp (x::=a) Q = (\<lambda>s. Q(s[a/x]))"
by (rule ext) (auto simp: wp_def)

lemma wp_Semi[simp]: "wp (c\<^isub>1;c\<^isub>2) Q = wp c\<^isub>1 (wp c\<^isub>2 Q)"
by (rule ext) (auto simp: wp_def)

lemma wp_If[simp]:
 "wp (IF b THEN c\<^isub>1 ELSE c\<^isub>2) Q =
 (\<lambda>s. (bval b s \<longrightarrow> wp c\<^isub>1 Q s) \<and>  (\<not> bval b s \<longrightarrow> wp c\<^isub>2 Q s))"
by (rule ext) (auto simp: wp_def)

lemma wp_While_If:
 "wp (WHILE b DO c) Q s =
  wp (IF b THEN c;WHILE b DO c ELSE SKIP) Q s"
unfolding wp_def by (metis unfold_while)

lemma wp_While_True[simp]: "bval b s \<Longrightarrow>
  wp (WHILE b DO c) Q s = wp (c; WHILE b DO c) Q s"
by(simp add: wp_While_If)

lemma wp_While_False[simp]: "\<not> bval b s \<Longrightarrow> wp (WHILE b DO c) Q s = Q s"
by(simp add: wp_While_If)


subsection "Completeness"

lemma wp_is_pre: "\<turnstile> {wp c Q} c {Q}"
proof(induction c arbitrary: Q)
  case Semi thus ?case by(auto intro: Semi)
next
  case (If b c1 c2)
  let ?If = "IF b THEN c1 ELSE c2"
  show ?case
  proof(rule hoare.If)
    show "\<turnstile> {\<lambda>s. wp ?If Q s \<and> bval b s} c1 {Q}"
    proof(rule strengthen_pre[OF _ If(1)])
      show "\<forall>s. wp ?If Q s \<and> bval b s \<longrightarrow> wp c1 Q s" by auto
    qed
    show "\<turnstile> {\<lambda>s. wp ?If Q s \<and> \<not> bval b s} c2 {Q}"
    proof(rule strengthen_pre[OF _ If(2)])
      show "\<forall>s. wp ?If Q s \<and> \<not> bval b s \<longrightarrow> wp c2 Q s" by auto
    qed
  qed
next
  case (While b c)
  let ?w = "WHILE b DO c"
  have "\<turnstile> {wp ?w Q} ?w {\<lambda>s. wp ?w Q s \<and> \<not> bval b s}"
  proof(rule hoare.While)
    show "\<turnstile> {\<lambda>s. wp ?w Q s \<and> bval b s} c {wp ?w Q}"
    proof(rule strengthen_pre[OF _ While(1)])
      show "\<forall>s. wp ?w Q s \<and> bval b s \<longrightarrow> wp c (wp ?w Q) s" by auto
    qed
  qed
  thus ?case
  proof(rule weaken_post)
    show "\<forall>s. wp ?w Q s \<and> \<not> bval b s \<longrightarrow> Q s" by auto
  qed
qed auto

lemma hoare_relative_complete: assumes "\<Turnstile> {P}c{Q}" shows "\<turnstile> {P}c{Q}"
proof(rule strengthen_pre)
  show "\<forall>s. P s \<longrightarrow> wp c Q s" using assms
    by (auto simp: hoare_valid_def wp_def)
  show "\<turnstile> {wp c Q} c {Q}" by(rule wp_is_pre)
qed

end
