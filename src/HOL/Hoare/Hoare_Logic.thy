(*  Title:      HOL/Hoare/Hoare_Logic.thy
    Author:     Leonor Prensa Nieto & Tobias Nipkow
    Copyright   1998 TUM
    Author:     Walter Guttmann (extension to total-correctness proofs)

Sugared semantic embedding of Hoare logic.
Strictly speaking a shallow embedding (as implemented by Norbert Galm
following Mike Gordon) would suffice. Maybe the datatype com comes in useful
later.
*)

theory Hoare_Logic
imports Main
begin

type_synonym 'a bexp = "'a set"
type_synonym 'a assn = "'a set"
type_synonym 'a var = "'a \<Rightarrow> nat"

datatype 'a com =
  Basic "'a \<Rightarrow> 'a"
| Seq "'a com" "'a com"               ("(_;/ _)"      [61,60] 60)
| Cond "'a bexp" "'a com" "'a com"    ("(1IF _/ THEN _ / ELSE _/ FI)"  [0,0,0] 61)
| While "'a bexp" "'a assn" "'a var" "'a com"  ("(1WHILE _/ INV {_} / VAR {_} //DO _ /OD)"  [0,0,0,0] 61)

syntax
  "_whilePC" :: "'a bexp \<Rightarrow> 'a assn \<Rightarrow> 'a com \<Rightarrow> 'a com"  ("(1WHILE _/ INV {_} //DO _ /OD)"  [0,0,0] 61)
translations
  "WHILE b INV {x} DO c OD" \<rightharpoonup> "WHILE b INV {x} VAR {0} DO c OD"

abbreviation annskip ("SKIP") where "SKIP == Basic id"

type_synonym 'a sem = "'a => 'a => bool"

inductive Sem :: "'a com \<Rightarrow> 'a sem"
where
  "Sem (Basic f) s (f s)"
| "Sem c1 s s'' \<Longrightarrow> Sem c2 s'' s' \<Longrightarrow> Sem (c1;c2) s s'"
| "s \<in> b \<Longrightarrow> Sem c1 s s' \<Longrightarrow> Sem (IF b THEN c1 ELSE c2 FI) s s'"
| "s \<notin> b \<Longrightarrow> Sem c2 s s' \<Longrightarrow> Sem (IF b THEN c1 ELSE c2 FI) s s'"
| "s \<notin> b \<Longrightarrow> Sem (While b x y c) s s"
| "s \<in> b \<Longrightarrow> Sem c s s'' \<Longrightarrow> Sem (While b x y c) s'' s' \<Longrightarrow>
   Sem (While b x y c) s s'"

inductive_cases [elim!]:
  "Sem (Basic f) s s'" "Sem (c1;c2) s s'"
  "Sem (IF b THEN c1 ELSE c2 FI) s s'"

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
  where "Valid p c q \<equiv> \<forall>s s'. Sem c s s' \<longrightarrow> s \<in> p \<longrightarrow> s' \<in> q"

definition ValidTC :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a bexp \<Rightarrow> bool"
  where "ValidTC p c q \<equiv> \<forall>s . s \<in> p \<longrightarrow> (\<exists>t . Sem c s t \<and> t \<in> q)"

lemma tc_implies_pc:
  "ValidTC p c q \<Longrightarrow> Valid p c q"
  by (metis Sem_deterministic Valid_def ValidTC_def)

lemma tc_extract_function:
  "ValidTC p c q \<Longrightarrow> \<exists>f . \<forall>s . s \<in> p \<longrightarrow> f s \<in> q"
  by (metis ValidTC_def)

syntax
  "_assign" :: "idt => 'b => 'a com"  ("(2_ :=/ _)" [70, 65] 61)

syntax
 "_hoare_vars" :: "[idts, 'a assn,'a com,'a assn] => bool"
                 ("VARS _// {_} // _ // {_}" [0,0,55,0] 50)
syntax (output)
 "_hoare"      :: "['a assn,'a com,'a assn] => bool"
                 ("{_} // _ // {_}" [0,55,0] 50)

ML_file \<open>hoare_syntax.ML\<close>
parse_translation \<open>[(\<^syntax_const>\<open>_hoare_vars\<close>, K Hoare_Syntax.hoare_vars_tr)]\<close>
print_translation \<open>[(\<^const_syntax>\<open>Valid\<close>, K (Hoare_Syntax.spec_tr' \<^syntax_const>\<open>_hoare\<close>))]\<close>

syntax
 "_hoare_tc_vars" :: "[idts, 'a assn,'a com,'a assn] => bool"
                    ("VARS _// [_] // _ // [_]" [0,0,55,0] 50)
syntax (output)
 "_hoare_tc"      :: "['a assn,'a com,'a assn] => bool"
                    ("[_] // _ // [_]" [0,55,0] 50)

parse_translation \<open>[(\<^syntax_const>\<open>_hoare_tc_vars\<close>, K Hoare_Syntax.hoare_tc_vars_tr)]\<close>
print_translation \<open>[(\<^const_syntax>\<open>ValidTC\<close>, K (Hoare_Syntax.spec_tr' \<^syntax_const>\<open>_hoare_tc\<close>))]\<close>


lemma SkipRule: "p \<subseteq> q \<Longrightarrow> Valid p (Basic id) q"
by (auto simp:Valid_def)

lemma BasicRule: "p \<subseteq> {s. f s \<in> q} \<Longrightarrow> Valid p (Basic f) q"
by (auto simp:Valid_def)

lemma SeqRule: "Valid P c1 Q \<Longrightarrow> Valid Q c2 R \<Longrightarrow> Valid P (c1;c2) R"
by (auto simp:Valid_def)

lemma CondRule:
 "p \<subseteq> {s. (s \<in> b \<longrightarrow> s \<in> w) \<and> (s \<notin> b \<longrightarrow> s \<in> w')}
  \<Longrightarrow> Valid w c1 q \<Longrightarrow> Valid w' c2 q \<Longrightarrow> Valid p (Cond b c1 c2) q"
by (auto simp:Valid_def)

lemma While_aux:
  assumes "Sem (WHILE b INV {i} VAR {v} DO c OD) s s'"
  shows "\<forall>s s'. Sem c s s' \<longrightarrow> s \<in> I \<and> s \<in> b \<longrightarrow> s' \<in> I \<Longrightarrow>
    s \<in> I \<Longrightarrow> s' \<in> I \<and> s' \<notin> b"
  using assms
  by (induct "WHILE b INV {i} VAR {v} DO c OD" s s') auto

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
    shows "ValidTC p (c1;c2) r"
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

lemma Compl_Collect: "-(Collect b) = {x. \<not>(b x)}"
  by blast

lemmas AbortRule = SkipRule  \<comment> \<open>dummy version\<close>
ML_file \<open>hoare_tac.ML\<close>

method_setup vcg = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (Hoare.hoare_tac ctxt (K all_tac)))\<close>
  "verification condition generator"

method_setup vcg_simp = \<open>
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD' (Hoare.hoare_tac ctxt (asm_full_simp_tac ctxt)))\<close>
  "verification condition generator plus simplification"

method_setup vcg_tc = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (Hoare.hoare_tc_tac ctxt (K all_tac)))\<close>
  "verification condition generator"

method_setup vcg_tc_simp = \<open>
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD' (Hoare.hoare_tc_tac ctxt (asm_full_simp_tac ctxt)))\<close>
  "verification condition generator plus simplification"

end
