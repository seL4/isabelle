(* Author: Tobias Nipkow *)

subsubsection "VCG for Total Correctness With Logical Variables"

theory VCG_Total_EX2
imports Hoare_Total_EX2
begin

text \<open>
Theory \<open>VCG_Total_EX\<close> conatins a VCG built on top of a Hoare logic without logical variables.
As a result the completeness proof runs into a problem. This theory uses a Hoare logic
with logical variables and proves soundness and completeness.
\<close>

text\<open>Annotated commands: commands where loops are annotated with
invariants.\<close>

datatype acom =
  Askip                  ("SKIP") |
  Aassign vname aexp     ("(_ ::= _)" [1000, 61] 61) |
  Aseq   acom acom       ("_;;/ _"  [60, 61] 60) |
  Aif bexp acom acom     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61) |
  Awhile assn2 lvname bexp acom
    ("({_'/_}/ WHILE _/ DO _)"  [0, 0, 0, 61] 61)

notation com.SKIP ("SKIP")

text\<open>Strip annotations:\<close>

fun strip :: "acom \<Rightarrow> com" where
"strip SKIP = SKIP" |
"strip (x ::= a) = (x ::= a)" |
"strip (C\<^sub>1;; C\<^sub>2) = (strip C\<^sub>1;; strip C\<^sub>2)" |
"strip (IF b THEN C\<^sub>1 ELSE C\<^sub>2) = (IF b THEN strip C\<^sub>1 ELSE strip C\<^sub>2)" |
"strip ({_/_} WHILE b DO C) = (WHILE b DO strip C)"

text\<open>Weakest precondition from annotated commands:\<close>

fun pre :: "acom \<Rightarrow> assn2 \<Rightarrow> assn2" where
"pre SKIP Q = Q" |
"pre (x ::= a) Q = (\<lambda>l s. Q l (s(x := aval a s)))" |
"pre (C\<^sub>1;; C\<^sub>2) Q = pre C\<^sub>1 (pre C\<^sub>2 Q)" |
"pre (IF b THEN C\<^sub>1 ELSE C\<^sub>2) Q =
  (\<lambda>l s. if bval b s then pre C\<^sub>1 Q l s else pre C\<^sub>2 Q l s)" |
"pre ({I/x} WHILE b DO C) Q = (\<lambda>l s. \<exists>n. I (l(x:=n)) s)"

text\<open>Verification condition:\<close>

fun vc :: "acom \<Rightarrow> assn2 \<Rightarrow> bool" where
"vc SKIP Q = True" |
"vc (x ::= a) Q = True" |
"vc (C\<^sub>1;; C\<^sub>2) Q = (vc C\<^sub>1 (pre C\<^sub>2 Q) \<and> vc C\<^sub>2 Q)" |
"vc (IF b THEN C\<^sub>1 ELSE C\<^sub>2) Q = (vc C\<^sub>1 Q \<and> vc C\<^sub>2 Q)" |
"vc ({I/x} WHILE b DO C) Q =
  (\<forall>l s. (I (l(x:=Suc(l x))) s \<longrightarrow> pre C I l s) \<and>
       (l x > 0 \<and> I l s \<longrightarrow> bval b s) \<and>
       (I (l(x := 0)) s \<longrightarrow> \<not> bval b s \<and> Q l s) \<and>
       vc C I)"

lemma vc_sound: "vc C Q \<Longrightarrow> \<turnstile>\<^sub>t {pre C Q} strip C {Q}"
proof(induction C arbitrary: Q)
  case (Awhile I x b C)
  show ?case
  proof(simp, rule weaken_post[OF While[of I x]], goal_cases)
    case 1 show ?case
      using Awhile.IH[of "I"] Awhile.prems by (auto intro: strengthen_pre)
  next
    case 3 show ?case
      using Awhile.prems by (simp) (metis fun_upd_triv)
  qed (insert Awhile.prems, auto)
qed (auto intro: conseq Seq If simp: Skip Assign)


text\<open>Completeness:\<close>

lemma pre_mono:
  "\<forall>l s. P l s \<longrightarrow> P' l s \<Longrightarrow> pre C P l s \<Longrightarrow> pre C P' l s"
proof (induction C arbitrary: P P' l s)
  case Aseq thus ?case by simp metis
qed simp_all

lemma vc_mono:
  "\<forall>l s. P l s \<longrightarrow> P' l s \<Longrightarrow> vc C P \<Longrightarrow> vc C P'"
proof(induction C arbitrary: P P')
  case Aseq thus ?case by simp (metis pre_mono)
qed simp_all

lemma vc_complete:
 "\<turnstile>\<^sub>t {P}c{Q} \<Longrightarrow> \<exists>C. strip C = c \<and> vc C Q \<and> (\<forall>l s. P l s \<longrightarrow> pre C Q l s)"
  (is "_ \<Longrightarrow> \<exists>C. ?G P c Q C")
proof (induction rule: hoaret.induct)
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
  from If.IH obtain C1 where ih1: "?G (\<lambda>l s. P l s \<and> bval b s) c1 Q C1"
    by blast
  from If.IH obtain C2 where ih2: "?G (\<lambda>l s. P l s \<and> \<not>bval b s) c2 Q C2"
    by blast
  show ?case (is "\<exists>C. ?C C")
  proof
    show "?C(Aif b C1 C2)" using ih1 ih2 by simp
  qed
next
  case (While P x c b)
  from While.IH obtain C where
    ih: "?G (\<lambda>l s. P (l(x:=Suc(l x))) s \<and> bval b s) c P C"
    by blast
  show ?case (is "\<exists>C. ?C C")
  proof
    have "vc ({P/x} WHILE b DO C) (\<lambda>l. P (l(x := 0)))"
      using ih While.hyps(2,3)
      by simp (metis fun_upd_same zero_less_Suc)
    thus "?C(Awhile P x b C)" using ih by simp
 qed
next
  case conseq thus ?case by(fast elim!: pre_mono vc_mono)
qed


text \<open>Two examples:\<close>

lemma vc1: "vc
 ({\<lambda>l s. l ''x'' = nat(s ''x'') / ''x''} WHILE Less (N 0) (V ''x'') DO ''x'' ::= Plus (V ''x'') (N (-1)))
 (\<lambda>l s. s ''x'' \<le> 0)"
by auto

thm vc_sound[OF vc1, simplified]

lemma vc2: "vc 
 ({\<lambda>l s. l ''x'' = nat(s ''x'') / ''x''} WHILE Less (N 0) (V ''x'')
 DO (''x'' ::= Plus (V ''x'') (N (-1));;
    (''y'' ::= V ''x'';;
     {\<lambda>l s. l ''x'' = nat(s ''x'') \<and> l ''y'' = nat(s ''y'') / ''y''}
     WHILE Less (N 0) (V ''y'') DO ''y'' ::= Plus (V ''y'') (N (-1)))))
(\<lambda>l s. s ''x'' \<le> 0)"
by auto

thm vc_sound[OF vc2, simplified]

end
