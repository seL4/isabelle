(*  Title:      HOL/Hoare/Hoare_Logic.thy
    Author:     Leonor Prensa Nieto & Tobias Nipkow
    Copyright   1998 TUM
    Author:     Walter Guttmann (extension to total-correctness proofs)
*)

section \<open>Sugared semantic embedding of Hoare logic\<close>

text \<open>
  Strictly speaking a shallow embedding (as implemented by Norbert Galm
  following Mike Gordon) would suffice. Maybe the datatype com comes in useful
  later.
\<close>

theory Hoare_Logic
imports Hoare_Syntax Hoare_Tac
begin

type_synonym 'a bexp = "'a set"
type_synonym 'a assn = "'a set"
type_synonym 'a var = "'a \<Rightarrow> nat"

datatype 'a com =
  Basic "'a \<Rightarrow> 'a"
| Seq "'a com" "'a com"
| Cond "'a bexp" "'a com" "'a com"
| While "'a bexp" "'a assn" "'a var" "'a com"

abbreviation annskip ("SKIP") where "SKIP == Basic id"

type_synonym 'a sem = "'a => 'a => bool"

inductive Sem :: "'a com \<Rightarrow> 'a sem"
where
  "Sem (Basic f) s (f s)"
| "Sem c1 s s'' \<Longrightarrow> Sem c2 s'' s' \<Longrightarrow> Sem (Seq c1 c2) s s'"
| "s \<in> b \<Longrightarrow> Sem c1 s s' \<Longrightarrow> Sem (Cond b c1 c2) s s'"
| "s \<notin> b \<Longrightarrow> Sem c2 s s' \<Longrightarrow> Sem (Cond b c1 c2) s s'"
| "s \<notin> b \<Longrightarrow> Sem (While b x y c) s s"
| "s \<in> b \<Longrightarrow> Sem c s s'' \<Longrightarrow> Sem (While b x y c) s'' s' \<Longrightarrow>
   Sem (While b x y c) s s'"

definition Valid :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a bexp \<Rightarrow> bool"
  where "Valid p c q \<equiv> \<forall>s s'. Sem c s s' \<longrightarrow> s \<in> p \<longrightarrow> s' \<in> q"

definition ValidTC :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a bexp \<Rightarrow> bool"
  where "ValidTC p c q \<equiv> \<forall>s. s \<in> p \<longrightarrow> (\<exists>t. Sem c s t \<and> t \<in> q)"

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

lemma tc_implies_pc:
  "ValidTC p c q \<Longrightarrow> Valid p c q"
  by (metis Sem_deterministic Valid_def ValidTC_def)

lemma tc_extract_function:
  "ValidTC p c q \<Longrightarrow> \<exists>f . \<forall>s . s \<in> p \<longrightarrow> f s \<in> q"
  by (metis ValidTC_def)


lemma SkipRule: "p \<subseteq> q \<Longrightarrow> Valid p (Basic id) q"
by (auto simp:Valid_def)

lemma BasicRule: "p \<subseteq> {s. f s \<in> q} \<Longrightarrow> Valid p (Basic f) q"
by (auto simp:Valid_def)

lemma SeqRule: "Valid P c1 Q \<Longrightarrow> Valid Q c2 R \<Longrightarrow> Valid P (Seq c1 c2) R"
by (auto simp:Valid_def)

lemma CondRule:
 "p \<subseteq> {s. (s \<in> b \<longrightarrow> s \<in> w) \<and> (s \<notin> b \<longrightarrow> s \<in> w')}
  \<Longrightarrow> Valid w c1 q \<Longrightarrow> Valid w' c2 q \<Longrightarrow> Valid p (Cond b c1 c2) q"
by (auto simp:Valid_def)

lemma While_aux:
  assumes "Sem (While b i v c) s s'"
  shows "\<forall>s s'. Sem c s s' \<longrightarrow> s \<in> I \<and> s \<in> b \<longrightarrow> s' \<in> I \<Longrightarrow>
    s \<in> I \<Longrightarrow> s' \<in> I \<and> s' \<notin> b"
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

lemma SkipRuleTC:
  assumes "p \<subseteq> q"
    shows "ValidTC p (Basic id) q"
  by (metis assms Sem.intros(1) ValidTC_def id_apply subsetD)

lemma BasicRuleTC:
  assumes "p \<subseteq> {s. f s \<in> q}"
    shows "ValidTC p (Basic f) q"
  by (metis assms Ball_Collect Sem.intros(1) ValidTC_def)

lemma SeqRuleTC:
  assumes "ValidTC p c1 q"
      and "ValidTC q c2 r"
    shows "ValidTC p (Seq c1 c2) r"
  by (meson assms Sem.intros(2) ValidTC_def)

lemma CondRuleTC:
 assumes "p \<subseteq> {s. (s \<in> b \<longrightarrow> s \<in> w) \<and> (s \<notin> b \<longrightarrow> s \<in> w')}"
     and "ValidTC w c1 q"
     and "ValidTC w' c2 q"
   shows "ValidTC p (Cond b c1 c2) q"
proof (unfold ValidTC_def, rule allI)
  fix s
  show "s \<in> p \<longrightarrow> (\<exists>t . Sem (Cond b c1 c2) s t \<and> t \<in> q)"
    apply (cases "s \<in> b")
    apply (metis (mono_tags, lifting) assms(1,2) Ball_Collect Sem.intros(3) ValidTC_def)
    by (metis (mono_tags, lifting) assms(1,3) Ball_Collect Sem.intros(4) ValidTC_def)
qed

lemma WhileRuleTC:
  assumes "p \<subseteq> i"
      and "\<And>n::nat . ValidTC (i \<inter> b \<inter> {s . v s = n}) c (i \<inter> {s . v s < n})"
      and "i \<inter> uminus b \<subseteq> q"
    shows "ValidTC p (While b i v c) q"
proof -
  {
    fix s n
    have "s \<in> i \<and> v s = n \<longrightarrow> (\<exists>t . Sem (While b i v c) s t \<and> t \<in> q)"
    proof (induction "n" arbitrary: s rule: less_induct)
      fix n :: nat
      fix s :: 'a
      assume 1: "\<And>(m::nat) s::'a . m < n \<Longrightarrow> s \<in> i \<and> v s = m \<longrightarrow> (\<exists>t . Sem (While b i v c) s t \<and> t \<in> q)"
      show "s \<in> i \<and> v s = n \<longrightarrow> (\<exists>t . Sem (While b i v c) s t \<and> t \<in> q)"
      proof (rule impI, cases "s \<in> b")
        assume 2: "s \<in> b" and "s \<in> i \<and> v s = n"
        hence "s \<in> i \<inter> b \<inter> {s . v s = n}"
          using assms(1) by auto
        hence "\<exists>t . Sem c s t \<and> t \<in> i \<inter> {s . v s < n}"
          by (metis assms(2) ValidTC_def)
        from this obtain t where 3: "Sem c s t \<and> t \<in> i \<inter> {s . v s < n}"
          by auto
        hence "\<exists>u . Sem (While b i v c) t u \<and> u \<in> q"
          using 1 by auto
        thus "\<exists>t . Sem (While b i v c) s t \<and> t \<in> q"
          using 2 3 Sem.intros(6) by force
      next
        assume "s \<notin> b" and "s \<in> i \<and> v s = n"
        thus "\<exists>t . Sem (While b i v c) s t \<and> t \<in> q"
          using Sem.intros(5) assms(3) by fastforce
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


subsection \<open>Proof methods: VCG\<close>

declare BasicRule [Hoare_Tac.BasicRule]
  and SkipRule [Hoare_Tac.SkipRule]
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
