(*  Title:      HOL/IMP/Hoare_Op.thy
    ID:         $Id$
    Author:     Tobias Nipkow
*)

header "Soundness and Completeness wrt Operational Semantics"

theory Hoare_Op imports Hoare begin

definition
  hoare_valid :: "[assn,com,assn] => bool" ("|= {(1_)}/ (_)/ {(1_)}" 50) where
  "|= {P}c{Q} = (!s t. \<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t --> P s --> Q t)"

lemma hoare_sound: "|- {P}c{Q} ==> |= {P}c{Q}"
proof(induct rule: hoare.induct)
  case (While P b c)
  { fix s t
    assume "\<langle>WHILE b DO c,s\<rangle> \<longrightarrow>\<^sub>c t"
    hence "P s \<longrightarrow> P t \<and> \<not> b t"
    proof(induct "WHILE b DO c" s t)
      case WhileFalse thus ?case by blast
    next
      case WhileTrue thus ?case
        using While(2) unfolding hoare_valid_def by blast
    qed

  }
  thus ?case unfolding hoare_valid_def by blast
qed (auto simp: hoare_valid_def)

definition
  wp :: "com => assn => assn" where
  "wp c Q = (%s. !t. \<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t --> Q t)"

lemma wp_SKIP: "wp \<SKIP> Q = Q"
by (simp add: wp_def)

lemma wp_Ass: "wp (x:==a) Q = (%s. Q(s[x\<mapsto>a s]))"
by (simp add: wp_def)

lemma wp_Semi: "wp (c;d) Q = wp c (wp d Q)"
by (rule ext) (auto simp: wp_def)

lemma wp_If:
 "wp (\<IF> b \<THEN> c \<ELSE> d) Q = (%s. (b s --> wp c Q s) &  (~b s --> wp d Q s))"
by (rule ext) (auto simp: wp_def)

lemma wp_While_If:
 "wp (\<WHILE> b \<DO> c) Q s =
  wp (IF b THEN c;\<WHILE> b \<DO> c ELSE SKIP) Q s"
unfolding wp_def by (metis equivD1 equivD2 unfold_while)

lemma wp_While_True: "b s ==>
  wp (\<WHILE> b \<DO> c) Q s = wp (c;\<WHILE> b \<DO> c) Q s"
by(simp add: wp_While_If wp_If wp_SKIP)

lemma wp_While_False: "~b s ==> wp (\<WHILE> b \<DO> c) Q s = Q s"
by(simp add: wp_While_If wp_If wp_SKIP)

lemmas [simp] = wp_SKIP wp_Ass wp_Semi wp_If wp_While_True wp_While_False

lemma wp_is_pre: "|- {wp c Q} c {Q}"
proof(induct c arbitrary: Q)
  case SKIP show ?case by auto
next
  case Assign show ?case by auto
next
  case Semi thus ?case by(auto intro: semi)
next
  case (Cond b c1 c2)
  let ?If = "IF b THEN c1 ELSE c2"
  show ?case
  proof(rule If)
    show "|- {\<lambda>s. wp ?If Q s \<and> b s} c1 {Q}"
    proof(rule strengthen_pre[OF _ Cond(1)])
      show "\<forall>s. wp ?If Q s \<and> b s \<longrightarrow> wp c1 Q s" by auto
    qed
    show "|- {\<lambda>s. wp ?If Q s \<and> \<not> b s} c2 {Q}"
    proof(rule strengthen_pre[OF _ Cond(2)])
      show "\<forall>s. wp ?If Q s \<and> \<not> b s \<longrightarrow> wp c2 Q s" by auto
    qed
  qed
next
  case (While b c)
  let ?w = "WHILE b DO c"
  have "|- {wp ?w Q} ?w {\<lambda>s. wp ?w Q s \<and> \<not> b s}"
  proof(rule hoare.While)
    show "|- {\<lambda>s. wp ?w Q s \<and> b s} c {wp ?w Q}"
    proof(rule strengthen_pre[OF _ While(1)])
      show "\<forall>s. wp ?w Q s \<and> b s \<longrightarrow> wp c (wp ?w Q) s" by auto
    qed
  qed
  thus ?case
  proof(rule weaken_post)
    show "\<forall>s. wp ?w Q s \<and> \<not> b s \<longrightarrow> Q s" by auto
  qed
qed

lemma hoare_relative_complete: assumes "|= {P}c{Q}" shows "|- {P}c{Q}"
proof(rule strengthen_pre)
  show "\<forall>s. P s \<longrightarrow> wp c Q s" using assms
    by (auto simp: hoare_valid_def wp_def)
  show "|- {wp c Q} c {Q}" by(rule wp_is_pre)
qed

end
