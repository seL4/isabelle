(*  Title:      HOL/Hoare/Hoare_Logic_Abort.thy
    Author:     Leonor Prensa Nieto & Tobias Nipkow
    Copyright   2003 TUM

Like Hoare.thy, but with an Abort statement for modelling run time errors.
*)

theory Hoare_Logic_Abort
imports Main
begin

type_synonym 'a bexp = "'a set"
type_synonym 'a assn = "'a set"

datatype
 'a com = Basic "'a \<Rightarrow> 'a"
   | Abort
   | Seq "'a com" "'a com"               ("(_;/ _)"      [61,60] 60)
   | Cond "'a bexp" "'a com" "'a com"    ("(1IF _/ THEN _ / ELSE _/ FI)"  [0,0,0] 61)
   | While "'a bexp" "'a assn" "'a com"  ("(1WHILE _/ INV {_} //DO _ /OD)"  [0,0,0] 61)

abbreviation annskip ("SKIP") where "SKIP == Basic id"

type_synonym 'a sem = "'a option => 'a option => bool"

inductive Sem :: "'a com \<Rightarrow> 'a sem"
where
  "Sem (Basic f) None None"
| "Sem (Basic f) (Some s) (Some (f s))"
| "Sem Abort s None"
| "Sem c1 s s'' \<Longrightarrow> Sem c2 s'' s' \<Longrightarrow> Sem (c1;c2) s s'"
| "Sem (IF b THEN c1 ELSE c2 FI) None None"
| "s \<in> b \<Longrightarrow> Sem c1 (Some s) s' \<Longrightarrow> Sem (IF b THEN c1 ELSE c2 FI) (Some s) s'"
| "s \<notin> b \<Longrightarrow> Sem c2 (Some s) s' \<Longrightarrow> Sem (IF b THEN c1 ELSE c2 FI) (Some s) s'"
| "Sem (While b x c) None None"
| "s \<notin> b \<Longrightarrow> Sem (While b x c) (Some s) (Some s)"
| "s \<in> b \<Longrightarrow> Sem c (Some s) s'' \<Longrightarrow> Sem (While b x c) s'' s' \<Longrightarrow>
   Sem (While b x c) (Some s) s'"

inductive_cases [elim!]:
  "Sem (Basic f) s s'" "Sem (c1;c2) s s'"
  "Sem (IF b THEN c1 ELSE c2 FI) s s'"

definition Valid :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a bexp \<Rightarrow> bool" where
  "Valid p c q == \<forall>s s'. Sem c s s' \<longrightarrow> s : Some ` p \<longrightarrow> s' : Some ` q"


syntax
  "_assign" :: "idt => 'b => 'a com"  ("(2_ :=/ _)" [70, 65] 61)

syntax
  "_hoare_abort_vars" :: "[idts, 'a assn,'a com,'a assn] => bool"
                 ("VARS _// {_} // _ // {_}" [0,0,55,0] 50)
syntax ("" output)
  "_hoare_abort"      :: "['a assn,'a com,'a assn] => bool"
                 ("{_} // _ // {_}" [0,55,0] 50)

ML_file "hoare_syntax.ML"
parse_translation {* [(@{syntax_const "_hoare_abort_vars"}, Hoare_Syntax.hoare_vars_tr)] *}
print_translation
  {* [(@{const_syntax Valid}, Hoare_Syntax.spec_tr' @{syntax_const "_hoare_abort"})] *}


(*** The proof rules ***)

lemma SkipRule: "p \<subseteq> q \<Longrightarrow> Valid p (Basic id) q"
by (auto simp:Valid_def)

lemma BasicRule: "p \<subseteq> {s. f s \<in> q} \<Longrightarrow> Valid p (Basic f) q"
by (auto simp:Valid_def)

lemma SeqRule: "Valid P c1 Q \<Longrightarrow> Valid Q c2 R \<Longrightarrow> Valid P (c1;c2) R"
by (auto simp:Valid_def)

lemma CondRule:
 "p \<subseteq> {s. (s \<in> b \<longrightarrow> s \<in> w) \<and> (s \<notin> b \<longrightarrow> s \<in> w')}
  \<Longrightarrow> Valid w c1 q \<Longrightarrow> Valid w' c2 q \<Longrightarrow> Valid p (Cond b c1 c2) q"
by (fastforce simp:Valid_def image_def)

lemma While_aux:
  assumes "Sem (WHILE b INV {i} DO c OD) s s'"
  shows "\<forall>s s'. Sem c s s' \<longrightarrow> s \<in> Some ` (I \<inter> b) \<longrightarrow> s' \<in> Some ` I \<Longrightarrow>
    s \<in> Some ` I \<Longrightarrow> s' \<in> Some ` (I \<inter> -b)"
  using assms
  by (induct "WHILE b INV {i} DO c OD" s s') auto

lemma WhileRule:
 "p \<subseteq> i \<Longrightarrow> Valid (i \<inter> b) c i \<Longrightarrow> i \<inter> (-b) \<subseteq> q \<Longrightarrow> Valid p (While b i c) q"
apply(simp add:Valid_def)
apply(simp (no_asm) add:image_def)
apply clarify
apply(drule While_aux)
  apply assumption
 apply blast
apply blast
done

lemma AbortRule: "p \<subseteq> {s. False} \<Longrightarrow> Valid p Abort q"
by(auto simp:Valid_def)


subsection {* Derivation of the proof rules and, most importantly, the VCG tactic *}

lemma Compl_Collect: "-(Collect b) = {x. ~(b x)}"
  by blast

ML_file "hoare_tac.ML"

method_setup vcg = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (hoare_tac ctxt (K all_tac))) *}
  "verification condition generator"

method_setup vcg_simp = {*
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD' (hoare_tac ctxt (asm_full_simp_tac (simpset_of ctxt)))) *}
  "verification condition generator plus simplification"

(* Special syntax for guarded statements and guarded array updates: *)

syntax
  "_guarded_com" :: "bool \<Rightarrow> 'a com \<Rightarrow> 'a com"  ("(2_ \<rightarrow>/ _)" 71)
  "_array_update" :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a com"  ("(2_[_] :=/ _)" [70, 65] 61)
translations
  "P \<rightarrow> c" == "IF P THEN c ELSE CONST Abort FI"
  "a[i] := v" => "(i < CONST length a) \<rightarrow> (a := CONST list_update a i v)"
  (* reverse translation not possible because of duplicate "a" *)

text{* Note: there is no special syntax for guarded array access. Thus
you must write @{text"j < length a \<rightarrow> a[i] := a!j"}. *}

end
