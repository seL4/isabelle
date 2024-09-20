(* Author: Tobias Nipkow *)

subsection "Verification Conditions for Total Correctness"

subsubsection "The Standard Approach"

theory VCG_Total_EX
imports Hoare_Total_EX
begin

text\<open>Annotated commands: commands where loops are annotated with
invariants.\<close>

datatype acom =
  Askip                  (\<open>SKIP\<close>) |
  Aassign vname aexp     (\<open>(_ ::= _)\<close> [1000, 61] 61) |
  Aseq   acom acom       (\<open>_;;/ _\<close>  [60, 61] 60) |
  Aif bexp acom acom     (\<open>(IF _/ THEN _/ ELSE _)\<close>  [0, 0, 61] 61) |
  Awhile "nat \<Rightarrow> assn" bexp acom
    (\<open>({_}/ WHILE _/ DO _)\<close>  [0, 0, 61] 61)

notation com.SKIP (\<open>SKIP\<close>)

text\<open>Strip annotations:\<close>

fun strip :: "acom \<Rightarrow> com" where
"strip SKIP = SKIP" |
"strip (x ::= a) = (x ::= a)" |
"strip (C\<^sub>1;; C\<^sub>2) = (strip C\<^sub>1;; strip C\<^sub>2)" |
"strip (IF b THEN C\<^sub>1 ELSE C\<^sub>2) = (IF b THEN strip C\<^sub>1 ELSE strip C\<^sub>2)" |
"strip ({_} WHILE b DO C) = (WHILE b DO strip C)"

text\<open>Weakest precondition from annotated commands:\<close>

fun pre :: "acom \<Rightarrow> assn \<Rightarrow> assn" where
"pre SKIP Q = Q" |
"pre (x ::= a) Q = (\<lambda>s. Q(s(x := aval a s)))" |
"pre (C\<^sub>1;; C\<^sub>2) Q = pre C\<^sub>1 (pre C\<^sub>2 Q)" |
"pre (IF b THEN C\<^sub>1 ELSE C\<^sub>2) Q =
  (\<lambda>s. if bval b s then pre C\<^sub>1 Q s else pre C\<^sub>2 Q s)" |
"pre ({I} WHILE b DO C) Q = (\<lambda>s. \<exists>n. I n s)"

text\<open>Verification condition:\<close>

fun vc :: "acom \<Rightarrow> assn \<Rightarrow> bool" where
"vc SKIP Q = True" |
"vc (x ::= a) Q = True" |
"vc (C\<^sub>1;; C\<^sub>2) Q = (vc C\<^sub>1 (pre C\<^sub>2 Q) \<and> vc C\<^sub>2 Q)" |
"vc (IF b THEN C\<^sub>1 ELSE C\<^sub>2) Q = (vc C\<^sub>1 Q \<and> vc C\<^sub>2 Q)" |
"vc ({I} WHILE b DO C) Q =
  (\<forall>s n. (I (Suc n) s \<longrightarrow> pre C (I n) s) \<and>
       (I (Suc n) s \<longrightarrow> bval b s) \<and>
       (I 0 s \<longrightarrow> \<not> bval b s \<and> Q s) \<and>
       vc C (I n))"

lemma vc_sound: "vc C Q \<Longrightarrow> \<turnstile>\<^sub>t {pre C Q} strip C {Q}"
proof(induction C arbitrary: Q)
  case (Awhile I b C)
  show ?case
  proof(simp, rule conseq[OF _ While[of I]], goal_cases)
    case (2 n) show ?case
      using Awhile.IH[of "I n"] Awhile.prems
      by (auto intro: strengthen_pre)
  qed (insert Awhile.prems, auto)
qed (auto intro: conseq Seq If simp: Skip Assign)

text\<open>When trying to extend the completeness proof of the VCG for partial correctness
to total correctness one runs into the following problem.
In the case of the while-rule, the universally quantified \<open>n\<close> in the first premise
means that for that premise the induction hypothesis does not yield a single
annotated command \<open>C\<close> but merely that for every \<open>n\<close> such a \<open>C\<close> exists.\<close>

end
