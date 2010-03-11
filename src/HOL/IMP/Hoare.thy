(*  Title:      HOL/IMP/Hoare.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TUM
*)

header "Inductive Definition of Hoare Logic"

theory Hoare imports Denotation begin

types assn = "state => bool"

definition
  hoare_valid :: "[assn,com,assn] => bool" ("|= {(1_)}/ (_)/ {(1_)}" 50) where
  "|= {P}c{Q} = (!s t. (s,t) : C(c) --> P s --> Q t)"

inductive
  hoare :: "assn => com => assn => bool" ("|- ({(1_)}/ (_)/ {(1_)})" 50)
where
  skip: "|- {P}\<SKIP>{P}"
| ass:  "|- {%s. P(s[x\<mapsto>a s])} x:==a {P}"
| semi: "[| |- {P}c{Q}; |- {Q}d{R} |] ==> |- {P} c;d {R}"
| If: "[| |- {%s. P s & b s}c{Q}; |- {%s. P s & ~b s}d{Q} |] ==>
      |- {P} \<IF> b \<THEN> c \<ELSE> d {Q}"
| While: "|- {%s. P s & b s} c {P} ==>
         |- {P} \<WHILE> b \<DO> c {%s. P s & ~b s}"
| conseq: "[| !s. P' s --> P s; |- {P}c{Q}; !s. Q s --> Q' s |] ==>
          |- {P'}c{Q'}"

definition
  wp :: "com => assn => assn" where
  "wp c Q = (%s. !t. (s,t) : C(c) --> Q t)"

(*
Soundness (and part of) relative completeness of Hoare rules
wrt denotational semantics
*)

lemma strengthen_pre: "[| !s. P' s --> P s; |- {P}c{Q} |] ==> |- {P'}c{Q}"
by (blast intro: conseq)

lemma weaken_post: "[| |- {P}c{Q}; !s. Q s --> Q' s |] ==> |- {P}c{Q'}"
by (blast intro: conseq)

lemma hoare_sound: "|- {P}c{Q} ==> |= {P}c{Q}"
proof(induct rule: hoare.induct)
  case (While P b c)
  { fix s t
    let ?G = "Gamma b (C c)"
    assume "(s,t) \<in> lfp ?G"
    hence "P s \<longrightarrow> P t \<and> \<not> b t"
    proof(rule lfp_induct2)
      show "mono ?G" by(rule Gamma_mono)
    next
      fix s t assume "(s,t) \<in> ?G (lfp ?G \<inter> {(s,t). P s \<longrightarrow> P t \<and> \<not> b t})"
      thus "P s \<longrightarrow> P t \<and> \<not> b t" using While.hyps
        by(auto simp: hoare_valid_def Gamma_def)
    qed
  }
  thus ?case by(simp add:hoare_valid_def)
qed (auto simp: hoare_valid_def)


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
by(simp only: wp_def C_While_If)

(*Not suitable for rewriting: LOOPS!*)
lemma wp_While_if:
  "wp (\<WHILE> b \<DO> c) Q s = (if b s then wp (c;\<WHILE> b \<DO> c) Q s else Q s)"
by(simp add:wp_While_If wp_If wp_SKIP)

lemma wp_While_True: "b s ==>
  wp (\<WHILE> b \<DO> c) Q s = wp (c;\<WHILE> b \<DO> c) Q s"
by(simp add: wp_While_if)

lemma wp_While_False: "~b s ==> wp (\<WHILE> b \<DO> c) Q s = Q s"
by(simp add: wp_While_if)

lemmas [simp] = wp_SKIP wp_Ass wp_Semi wp_If wp_While_True wp_While_False

lemma wp_While: "wp (\<WHILE> b \<DO> c) Q s =
   (s : gfp(%S.{s. if b s then wp c (%s. s:S) s else Q s}))"
apply (simp (no_asm))
apply (rule iffI)
 apply (rule weak_coinduct)
  apply (erule CollectI)
 apply safe
  apply simp
 apply simp
apply (simp add: wp_def Gamma_def)
apply (intro strip)
apply (rule mp)
 prefer 2 apply (assumption)
apply (erule lfp_induct2)
apply (fast intro!: monoI)
apply (subst gfp_unfold)
 apply (fast intro!: monoI)
apply fast
done

declare C_while [simp del]

lemmas [intro!] = hoare.skip hoare.ass hoare.semi hoare.If

lemma wp_is_pre: "|- {wp c Q} c {Q}"
proof(induct c arbitrary: Q)
  case SKIP show ?case by auto
next
  case Assign show ?case by auto
next
  case Semi thus ?case by auto
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
proof(rule conseq)
  show "\<forall>s. P s \<longrightarrow> wp c Q s" using assms
    by (auto simp: hoare_valid_def wp_def)
  show "|- {wp c Q} c {Q}" by(rule wp_is_pre)
  show "\<forall>s. Q s \<longrightarrow> Q s" by auto
qed

end
