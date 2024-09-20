(* Author: Tobias Nipkow *)

subsection "Verification Condition Generation"

theory VCG imports Hoare begin

subsubsection "Annotated Commands"

text\<open>Commands where loops are annotated with invariants.\<close>

datatype acom =
  Askip                  (\<open>SKIP\<close>) |
  Aassign vname aexp     (\<open>(_ ::= _)\<close> [1000, 61] 61) |
  Aseq   acom acom       (\<open>_;;/ _\<close>  [60, 61] 60) |
  Aif bexp acom acom     (\<open>(IF _/ THEN _/ ELSE _)\<close>  [0, 0, 61] 61) |
  Awhile assn bexp acom  (\<open>({_}/ WHILE _/ DO _)\<close>  [0, 0, 61] 61)

notation com.SKIP (\<open>SKIP\<close>)

text\<open>Strip annotations:\<close>

fun strip :: "acom \<Rightarrow> com" where
"strip SKIP = SKIP" |
"strip (x ::= a) = (x ::= a)" |
"strip (C\<^sub>1;; C\<^sub>2) = (strip C\<^sub>1;; strip C\<^sub>2)" |
"strip (IF b THEN C\<^sub>1 ELSE C\<^sub>2) = (IF b THEN strip C\<^sub>1 ELSE strip C\<^sub>2)" |
"strip ({_} WHILE b DO C) = (WHILE b DO strip C)"

subsubsection "Weeakest Precondistion and Verification Condition"

text\<open>Weakest precondition:\<close>

fun pre :: "acom \<Rightarrow> assn \<Rightarrow> assn" where
"pre SKIP Q = Q" |
"pre (x ::= a) Q = (\<lambda>s. Q(s(x := aval a s)))" |
"pre (C\<^sub>1;; C\<^sub>2) Q = pre C\<^sub>1 (pre C\<^sub>2 Q)" |
"pre (IF b THEN C\<^sub>1 ELSE C\<^sub>2) Q =
  (\<lambda>s. if bval b s then pre C\<^sub>1 Q s else pre C\<^sub>2 Q s)" |
"pre ({I} WHILE b DO C) Q = I"

text\<open>Verification condition:\<close>

fun vc :: "acom \<Rightarrow> assn \<Rightarrow> bool" where
"vc SKIP Q = True" |
"vc (x ::= a) Q = True" |
"vc (C\<^sub>1;; C\<^sub>2) Q = (vc C\<^sub>1 (pre C\<^sub>2 Q) \<and> vc C\<^sub>2 Q)" |
"vc (IF b THEN C\<^sub>1 ELSE C\<^sub>2) Q = (vc C\<^sub>1 Q \<and> vc C\<^sub>2 Q)" |
"vc ({I} WHILE b DO C) Q =
  ((\<forall>s. (I s \<and> bval b s \<longrightarrow> pre C I s) \<and>
        (I s \<and> \<not> bval b s \<longrightarrow> Q s)) \<and>
    vc C I)"


subsubsection "Soundness"

lemma vc_sound: "vc C Q \<Longrightarrow> \<turnstile> {pre C Q} strip C {Q}"
proof(induction C arbitrary: Q)
  case (Awhile I b C)
  show ?case
  proof(simp, rule While')
    from \<open>vc (Awhile I b C) Q\<close>
    have vc: "vc C I" and IQ: "\<forall>s. I s \<and> \<not> bval b s \<longrightarrow> Q s" and
         pre: "\<forall>s. I s \<and> bval b s \<longrightarrow> pre C I s" by simp_all
    have "\<turnstile> {pre C I} strip C {I}" by(rule Awhile.IH[OF vc])
    with pre show "\<turnstile> {\<lambda>s. I s \<and> bval b s} strip C {I}"
      by(rule strengthen_pre)
    show "\<forall>s. I s \<and> \<not>bval b s \<longrightarrow> Q s" by(rule IQ)
  qed
qed (auto intro: hoare.conseq)

corollary vc_sound':
  "\<lbrakk> vc C Q; \<forall>s. P s \<longrightarrow> pre C Q s \<rbrakk> \<Longrightarrow> \<turnstile> {P} strip C {Q}"
by (metis strengthen_pre vc_sound)


subsubsection "Completeness"

lemma pre_mono:
  "\<forall>s. P s \<longrightarrow> P' s \<Longrightarrow> pre C P s \<Longrightarrow> pre C P' s"
proof (induction C arbitrary: P P' s)
  case Aseq thus ?case by simp metis
qed simp_all

lemma vc_mono:
  "\<forall>s. P s \<longrightarrow> P' s \<Longrightarrow> vc C P \<Longrightarrow> vc C P'"
proof(induction C arbitrary: P P')
  case Aseq thus ?case by simp (metis pre_mono)
qed simp_all

lemma vc_complete:
 "\<turnstile> {P}c{Q} \<Longrightarrow> \<exists>C. strip C = c \<and> vc C Q \<and> (\<forall>s. P s \<longrightarrow> pre C Q s)"
  (is "_ \<Longrightarrow> \<exists>C. ?G P c Q C")
proof (induction rule: hoare.induct)
  case Skip
  show ?case (is "\<exists>C. ?C C")
  proof show "?C Askip" by simp qed
next
  case (Assign P a x)
  show ?case (is "\<exists>C. ?C C")
  proof show "?C(Aassign x a)" by simp qed
next
  case (Seq P c1 Q c2 R)
  from Seq.IH obtain C1 where ih1: "?G P c1 Q C1" by blast
  from Seq.IH obtain C2 where ih2: "?G Q c2 R C2" by blast
  show ?case (is "\<exists>C. ?C C")
  proof
    show "?C(Aseq C1 C2)"
      using ih1 ih2 by (fastforce elim!: pre_mono vc_mono)
  qed
next
  case (If P b c1 Q c2)
  from If.IH obtain C1 where ih1: "?G (\<lambda>s. P s \<and> bval b s) c1 Q C1"
    by blast
  from If.IH obtain C2 where ih2: "?G (\<lambda>s. P s \<and> \<not>bval b s) c2 Q C2"
    by blast
  show ?case (is "\<exists>C. ?C C")
  proof
    show "?C(Aif b C1 C2)" using ih1 ih2 by simp
  qed
next
  case (While P b c)
  from While.IH obtain C where ih: "?G (\<lambda>s. P s \<and> bval b s) c P C" by blast
  show ?case (is "\<exists>C. ?C C")
  proof show "?C(Awhile P b C)" using ih by simp qed
next
  case conseq thus ?case by(fast elim!: pre_mono vc_mono)
qed

end
