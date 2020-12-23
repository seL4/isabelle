(*  Title:      HOL/Hoare/Hoare_Logic_Abort.thy
    Author:     Leonor Prensa Nieto & Tobias Nipkow
    Copyright   2003 TUM
    Author:     Walter Guttmann (extension to total-correctness proofs)
*)

section \<open>Hoare Logic with an Abort statement for modelling run time errors\<close>

theory Hoare_Logic_Abort
  imports Hoare_Syntax Hoare_Tac
begin

type_synonym 'a bexp = "'a set"
type_synonym 'a assn = "'a set"
type_synonym 'a var = "'a \<Rightarrow> nat"

datatype 'a com =
  Basic "'a \<Rightarrow> 'a"
| Abort
| Seq "'a com" "'a com"
| Cond "'a bexp" "'a com" "'a com"
| While "'a bexp" "'a assn" "'a var" "'a com"

abbreviation annskip ("SKIP") where "SKIP == Basic id"

type_synonym 'a sem = "'a option => 'a option => bool"

inductive Sem :: "'a com \<Rightarrow> 'a sem"
where
  "Sem (Basic f) None None"
| "Sem (Basic f) (Some s) (Some (f s))"
| "Sem Abort s None"
| "Sem c1 s s'' \<Longrightarrow> Sem c2 s'' s' \<Longrightarrow> Sem (Seq c1 c2) s s'"
| "Sem (Cond b c1 c2) None None"
| "s \<in> b \<Longrightarrow> Sem c1 (Some s) s' \<Longrightarrow> Sem (Cond b c1 c2) (Some s) s'"
| "s \<notin> b \<Longrightarrow> Sem c2 (Some s) s' \<Longrightarrow> Sem (Cond b c1 c2) (Some s) s'"
| "Sem (While b x y c) None None"
| "s \<notin> b \<Longrightarrow> Sem (While b x y c) (Some s) (Some s)"
| "s \<in> b \<Longrightarrow> Sem c (Some s) s'' \<Longrightarrow> Sem (While b x y c) s'' s' \<Longrightarrow>
   Sem (While b x y c) (Some s) s'"

inductive_cases [elim!]:
  "Sem (Basic f) s s'" "Sem (Seq c1 c2) s s'"
  "Sem (Cond b c1 c2) s s'"

lemma Sem_deterministic:
  assumes "Sem c s s1"
      and "Sem c s s2"
    shows "s1 = s2"
proof -
  have "Sem c s s1 \<Longrightarrow> (\<forall>s2. Sem c s s2 \<longrightarrow> s1 = s2)"
    by (induct rule: Sem.induct) (subst Sem.simps, blast)+
  thus ?thesis
    using assms by simp
qed

definition Valid :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a bexp \<Rightarrow> bool"
  where "Valid p c q \<equiv> \<forall>s s'. Sem c s s' \<longrightarrow> s \<in> Some ` p \<longrightarrow> s' \<in> Some ` q"

definition ValidTC :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a bexp \<Rightarrow> bool"
  where "ValidTC p c q \<equiv> \<forall>s . s \<in> p \<longrightarrow> (\<exists>t . Sem c (Some s) (Some t) \<and> t \<in> q)"

lemma tc_implies_pc:
  "ValidTC p c q \<Longrightarrow> Valid p c q"
  by (smt Sem_deterministic ValidTC_def Valid_def image_iff)

lemma tc_extract_function:
  "ValidTC p c q \<Longrightarrow> \<exists>f . \<forall>s . s \<in> p \<longrightarrow> f s \<in> q"
  by (meson ValidTC_def)

text \<open>The proof rules for partial correctness\<close>

lemma SkipRule: "p \<subseteq> q \<Longrightarrow> Valid p (Basic id) q"
by (auto simp:Valid_def)

lemma BasicRule: "p \<subseteq> {s. f s \<in> q} \<Longrightarrow> Valid p (Basic f) q"
by (auto simp:Valid_def)

lemma SeqRule: "Valid P c1 Q \<Longrightarrow> Valid Q c2 R \<Longrightarrow> Valid P (Seq c1 c2) R"
by (auto simp:Valid_def)

lemma CondRule:
 "p \<subseteq> {s. (s \<in> b \<longrightarrow> s \<in> w) \<and> (s \<notin> b \<longrightarrow> s \<in> w')}
  \<Longrightarrow> Valid w c1 q \<Longrightarrow> Valid w' c2 q \<Longrightarrow> Valid p (Cond b c1 c2) q"
by (fastforce simp:Valid_def image_def)

lemma While_aux:
  assumes "Sem (While b i v c) s s'"
  shows "\<forall>s s'. Sem c s s' \<longrightarrow> s \<in> Some ` (I \<inter> b) \<longrightarrow> s' \<in> Some ` I \<Longrightarrow>
    s \<in> Some ` I \<Longrightarrow> s' \<in> Some ` (I \<inter> -b)"
  using assms
  by (induct "While b i v c" s s') auto

lemma WhileRule:
 "p \<subseteq> i \<Longrightarrow> Valid (i \<inter> b) c i \<Longrightarrow> i \<inter> (-b) \<subseteq> q \<Longrightarrow> Valid p (While b i v c) q"
apply (clarsimp simp:Valid_def)
apply(drule While_aux)
  apply assumption
 apply blast
apply blast
done

lemma AbortRule: "p \<subseteq> {s. False} \<Longrightarrow> Valid p Abort q"
by(auto simp:Valid_def)

text \<open>The proof rules for total correctness\<close>

lemma SkipRuleTC:
  assumes "p \<subseteq> q"
    shows "ValidTC p (Basic id) q"
  by (metis Sem.intros(2) ValidTC_def assms id_def subsetD)

lemma BasicRuleTC:
  assumes "p \<subseteq> {s. f s \<in> q}"
    shows "ValidTC p (Basic f) q"
  by (metis Ball_Collect Sem.intros(2) ValidTC_def assms)

lemma SeqRuleTC:
  assumes "ValidTC p c1 q"
      and "ValidTC q c2 r"
    shows "ValidTC p (Seq c1 c2) r"
  by (meson assms Sem.intros(4) ValidTC_def)

lemma CondRuleTC:
 assumes "p \<subseteq> {s. (s \<in> b \<longrightarrow> s \<in> w) \<and> (s \<notin> b \<longrightarrow> s \<in> w')}"
     and "ValidTC w c1 q"
     and "ValidTC w' c2 q"
   shows "ValidTC p (Cond b c1 c2) q"
proof (unfold ValidTC_def, rule allI)
  fix s
  show "s \<in> p \<longrightarrow> (\<exists>t . Sem (Cond b c1 c2) (Some s) (Some t) \<and> t \<in> q)"
    apply (cases "s \<in> b")
    apply (metis (mono_tags, lifting) Ball_Collect Sem.intros(6) ValidTC_def assms(1,2))
    by (metis (mono_tags, lifting) Ball_Collect Sem.intros(7) ValidTC_def assms(1,3))
qed

lemma WhileRuleTC:
  assumes "p \<subseteq> i"
      and "\<And>n::nat . ValidTC (i \<inter> b \<inter> {s . v s = n}) c (i \<inter> {s . v s < n})"
      and "i \<inter> uminus b \<subseteq> q"
    shows "ValidTC p (While b i v c) q"
proof -
  {
    fix s n
    have "s \<in> i \<and> v s = n \<longrightarrow> (\<exists>t . Sem (While b i v c) (Some s) (Some t) \<and> t \<in> q)"
    proof (induction "n" arbitrary: s rule: less_induct)
      fix n :: nat
      fix s :: 'a
      assume 1: "\<And>(m::nat) s::'a . m < n \<Longrightarrow> s \<in> i \<and> v s = m \<longrightarrow> (\<exists>t . Sem (While b i v c) (Some s) (Some t) \<and> t \<in> q)"
      show "s \<in> i \<and> v s = n \<longrightarrow> (\<exists>t . Sem (While b i v c) (Some s) (Some t) \<and> t \<in> q)"
      proof (rule impI, cases "s \<in> b")
        assume 2: "s \<in> b" and "s \<in> i \<and> v s = n"
        hence "s \<in> i \<inter> b \<inter> {s . v s = n}"
          using assms(1) by auto
        hence "\<exists>t . Sem c (Some s) (Some t) \<and> t \<in> i \<inter> {s . v s < n}"
          by (metis assms(2) ValidTC_def)
        from this obtain t where 3: "Sem c (Some s) (Some t) \<and> t \<in> i \<inter> {s . v s < n}"
          by auto
        hence "\<exists>u . Sem (While b i v c) (Some t) (Some u) \<and> u \<in> q"
          using 1 by auto
        thus "\<exists>t . Sem (While b i v c) (Some s) (Some t) \<and> t \<in> q"
          using 2 3 Sem.intros(10) by force
      next
        assume "s \<notin> b" and "s \<in> i \<and> v s = n"
        thus "\<exists>t . Sem (While b i v c) (Some s) (Some t) \<and> t \<in> q"
          using Sem.intros(9) assms(3) by fastforce
      qed
    qed
  }
  thus ?thesis
    using assms(1) ValidTC_def by force
qed


subsection \<open>Concrete syntax\<close>

setup \<open>
  Hoare_Syntax.setup
   {Basic = \<^const_syntax>\<open>Basic\<close>,
    Skip = \<^const_syntax>\<open>annskip\<close>,
    Seq = \<^const_syntax>\<open>Seq\<close>,
    Cond = \<^const_syntax>\<open>Cond\<close>,
    While = \<^const_syntax>\<open>While\<close>,
    Valid = \<^const_syntax>\<open>Valid\<close>,
    ValidTC = \<^const_syntax>\<open>ValidTC\<close>}
\<close>

\<comment> \<open>Special syntax for guarded statements and guarded array updates:\<close>
syntax
  "_guarded_com" :: "bool \<Rightarrow> 'a com \<Rightarrow> 'a com"  ("(2_ \<rightarrow>/ _)" 71)
  "_array_update" :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a com"  ("(2_[_] :=/ _)" [70, 65] 61)
translations
  "P \<rightarrow> c" \<rightleftharpoons> "IF P THEN c ELSE CONST Abort FI"
  "a[i] := v" \<rightharpoonup> "(i < CONST length a) \<rightarrow> (a := CONST list_update a i v)"
  \<comment> \<open>reverse translation not possible because of duplicate \<open>a\<close>\<close>

text \<open>
  Note: there is no special syntax for guarded array access. Thus
  you must write \<open>j < length a \<rightarrow> a[i] := a!j\<close>.
\<close>


subsection \<open>Proof methods: VCG\<close>

declare BasicRule [Hoare_Tac.BasicRule]
  and SkipRule [Hoare_Tac.SkipRule]
  and AbortRule [Hoare_Tac.AbortRule]
  and SeqRule [Hoare_Tac.SeqRule]
  and CondRule [Hoare_Tac.CondRule]
  and WhileRule [Hoare_Tac.WhileRule]

declare BasicRuleTC [Hoare_Tac.BasicRuleTC]
  and SkipRuleTC [Hoare_Tac.SkipRuleTC]
  and SeqRuleTC [Hoare_Tac.SeqRuleTC]
  and CondRuleTC [Hoare_Tac.CondRuleTC]
  and WhileRuleTC [Hoare_Tac.WhileRuleTC]

method_setup vcg = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (Hoare_Tac.hoare_tac ctxt (K all_tac)))\<close>
  "verification condition generator"

method_setup vcg_simp = \<open>
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD' (Hoare_Tac.hoare_tac ctxt (asm_full_simp_tac ctxt)))\<close>
  "verification condition generator plus simplification"

method_setup vcg_tc = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (Hoare_Tac.hoare_tc_tac ctxt (K all_tac)))\<close>
  "verification condition generator"

method_setup vcg_tc_simp = \<open>
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD' (Hoare_Tac.hoare_tc_tac ctxt (asm_full_simp_tac ctxt)))\<close>
  "verification condition generator plus simplification"

end
