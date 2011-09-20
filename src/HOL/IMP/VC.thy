header "Verification Conditions"

theory VC imports Hoare begin

subsection "VCG via Weakest Preconditions"

text{* Annotated commands: commands where loops are annotated with
invariants. *}

datatype acom = Askip
              | Aassign name aexp
              | Asemi   acom acom
              | Aif     bexp acom acom
              | Awhile  bexp assn acom

text{* Weakest precondition from annotated commands: *}

fun pre :: "acom \<Rightarrow> assn \<Rightarrow> assn" where
"pre Askip Q = Q" |
"pre (Aassign x a) Q = (\<lambda>s. Q(s(x := aval a s)))" |
"pre (Asemi c\<^isub>1 c\<^isub>2) Q = pre c\<^isub>1 (pre c\<^isub>2 Q)" |
"pre (Aif b c\<^isub>1 c\<^isub>2) Q =
  (\<lambda>s. (bval b s \<longrightarrow> pre c\<^isub>1 Q s) \<and>
       (\<not> bval b s \<longrightarrow> pre c\<^isub>2 Q s))" |
"pre (Awhile b I c) Q = I"

text{* Verification condition: *}

fun vc :: "acom \<Rightarrow> assn \<Rightarrow> assn" where
"vc Askip Q = (\<lambda>s. True)" |
"vc (Aassign x a) Q = (\<lambda>s. True)" |
"vc (Asemi c\<^isub>1 c\<^isub>2) Q = (\<lambda>s. vc c\<^isub>1 (pre c\<^isub>2 Q) s \<and> vc c\<^isub>2 Q s)" |
"vc (Aif b c\<^isub>1 c\<^isub>2) Q = (\<lambda>s. vc c\<^isub>1 Q s \<and> vc c\<^isub>2 Q s)" |
"vc (Awhile b I c) Q =
  (\<lambda>s. (I s \<and> \<not> bval b s \<longrightarrow> Q s) \<and>
       (I s \<and> bval b s \<longrightarrow> pre c I s) \<and>
       vc c I s)"

text{* Strip annotations: *}

fun astrip :: "acom \<Rightarrow> com" where
"astrip Askip = SKIP" |
"astrip (Aassign x a) = (x::=a)" |
"astrip (Asemi c\<^isub>1 c\<^isub>2) = (astrip c\<^isub>1; astrip c\<^isub>2)" |
"astrip (Aif b c\<^isub>1 c\<^isub>2) = (IF b THEN astrip c\<^isub>1 ELSE astrip c\<^isub>2)" |
"astrip (Awhile b I c) = (WHILE b DO astrip c)"


subsection "Soundness"

lemma vc_sound: "\<forall>s. vc c Q s \<Longrightarrow> \<turnstile> {pre c Q} astrip c {Q}"
proof(induction c arbitrary: Q)
  case (Awhile b I c)
  show ?case
  proof(simp, rule While')
    from `\<forall>s. vc (Awhile b I c) Q s`
    have vc: "\<forall>s. vc c I s" and IQ: "\<forall>s. I s \<and> \<not> bval b s \<longrightarrow> Q s" and
         pre: "\<forall>s. I s \<and> bval b s \<longrightarrow> pre c I s" by simp_all
    have "\<turnstile> {pre c I} astrip c {I}" by(rule Awhile.IH[OF vc])
    with pre show "\<turnstile> {\<lambda>s. I s \<and> bval b s} astrip c {I}"
      by(rule strengthen_pre)
    show "\<forall>s. I s \<and> \<not>bval b s \<longrightarrow> Q s" by(rule IQ)
  qed
qed (auto intro: hoare.conseq)

corollary vc_sound':
  "(\<forall>s. vc c Q s) \<and> (\<forall>s. P s \<longrightarrow> pre c Q s) \<Longrightarrow> \<turnstile> {P} astrip c {Q}"
by (metis strengthen_pre vc_sound)


subsection "Completeness"

lemma pre_mono:
  "\<forall>s. P s \<longrightarrow> P' s \<Longrightarrow> pre c P s \<Longrightarrow> pre c P' s"
proof (induction c arbitrary: P P' s)
  case Asemi thus ?case by simp metis
qed simp_all

lemma vc_mono:
  "\<forall>s. P s \<longrightarrow> P' s \<Longrightarrow> vc c P s \<Longrightarrow> vc c P' s"
proof(induction c arbitrary: P P')
  case Asemi thus ?case by simp (metis pre_mono)
qed simp_all

lemma vc_complete:
 "\<turnstile> {P}c{Q} \<Longrightarrow> \<exists>c'. astrip c' = c \<and> (\<forall>s. vc c' Q s) \<and> (\<forall>s. P s \<longrightarrow> pre c' Q s)"
  (is "_ \<Longrightarrow> \<exists>c'. ?G P c Q c'")
proof (induction rule: hoare.induct)
  case Skip
  show ?case (is "\<exists>ac. ?C ac")
  proof show "?C Askip" by simp qed
next
  case (Assign P a x)
  show ?case (is "\<exists>ac. ?C ac")
  proof show "?C(Aassign x a)" by simp qed
next
  case (Semi P c1 Q c2 R)
  from Semi.IH obtain ac1 where ih1: "?G P c1 Q ac1" by blast
  from Semi.IH obtain ac2 where ih2: "?G Q c2 R ac2" by blast
  show ?case (is "\<exists>ac. ?C ac")
  proof
    show "?C(Asemi ac1 ac2)"
      using ih1 ih2 by (fastforce elim!: pre_mono vc_mono)
  qed
next
  case (If P b c1 Q c2)
  from If.IH obtain ac1 where ih1: "?G (\<lambda>s. P s \<and> bval b s) c1 Q ac1"
    by blast
  from If.IH obtain ac2 where ih2: "?G (\<lambda>s. P s \<and> \<not>bval b s) c2 Q ac2"
    by blast
  show ?case (is "\<exists>ac. ?C ac")
  proof
    show "?C(Aif b ac1 ac2)" using ih1 ih2 by simp
  qed
next
  case (While P b c)
  from While.IH obtain ac where ih: "?G (\<lambda>s. P s \<and> bval b s) c P ac" by blast
  show ?case (is "\<exists>ac. ?C ac")
  proof show "?C(Awhile b P ac)" using ih by simp qed
next
  case conseq thus ?case by(fast elim!: pre_mono vc_mono)
qed


subsection "An Optimization"

fun vcpre :: "acom \<Rightarrow> assn \<Rightarrow> assn \<times> assn" where
"vcpre Askip Q = (\<lambda>s. True, Q)" |
"vcpre (Aassign x a) Q = (\<lambda>s. True, \<lambda>s. Q(s[a/x]))" |
"vcpre (Asemi c\<^isub>1 c\<^isub>2) Q =
  (let (vc\<^isub>2,wp\<^isub>2) = vcpre c\<^isub>2 Q;
       (vc\<^isub>1,wp\<^isub>1) = vcpre c\<^isub>1 wp\<^isub>2
   in (\<lambda>s. vc\<^isub>1 s \<and> vc\<^isub>2 s, wp\<^isub>1))" |
"vcpre (Aif b c\<^isub>1 c\<^isub>2) Q =
  (let (vc\<^isub>2,wp\<^isub>2) = vcpre c\<^isub>2 Q;
       (vc\<^isub>1,wp\<^isub>1) = vcpre c\<^isub>1 Q
   in (\<lambda>s. vc\<^isub>1 s \<and> vc\<^isub>2 s, \<lambda>s. (bval b s \<longrightarrow> wp\<^isub>1 s) \<and> (\<not>bval b s \<longrightarrow> wp\<^isub>2 s)))" |
"vcpre (Awhile b I c) Q =
  (let (vcc,wpc) = vcpre c I
   in (\<lambda>s. (I s \<and> \<not> bval b s \<longrightarrow> Q s) \<and>
           (I s \<and> bval b s \<longrightarrow> wpc s) \<and> vcc s, I))"

lemma vcpre_vc_pre: "vcpre c Q = (vc c Q, pre c Q)"
by (induct c arbitrary: Q) (simp_all add: Let_def)

end
