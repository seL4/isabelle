(*  Title:      HOL/Nitpick.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009, 2010

Nitpick: Yet another counterexample generator for Isabelle/HOL.
*)

header {* Nitpick: Yet Another Counterexample Generator for Isabelle/HOL *}

theory Nitpick
imports Map Quotient SAT Record
keywords "nitpick" :: diag and "nitpick_params" :: thy_decl
begin

typedecl bisim_iterator

axiomatization unknown :: 'a
           and is_unknown :: "'a \<Rightarrow> bool"
           and bisim :: "bisim_iterator \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
           and bisim_iterator_max :: bisim_iterator
           and Quot :: "'a \<Rightarrow> 'b"
           and safe_The :: "('a \<Rightarrow> bool) \<Rightarrow> 'a"

datatype ('a, 'b) fun_box = FunBox "('a \<Rightarrow> 'b)"
datatype ('a, 'b) pair_box = PairBox 'a 'b

typedecl unsigned_bit
typedecl signed_bit

datatype 'a word = Word "('a set)"

text {*
Alternative definitions.
*}

lemma Ex1_unfold [nitpick_unfold, no_atp]:
"Ex1 P \<equiv> \<exists>x. {x. P x} = {x}"
apply (rule eq_reflection)
apply (simp add: Ex1_def set_eq_iff)
apply (rule iffI)
 apply (erule exE)
 apply (erule conjE)
 apply (rule_tac x = x in exI)
 apply (rule allI)
 apply (rename_tac y)
 apply (erule_tac x = y in allE)
by auto

lemma rtrancl_unfold [nitpick_unfold, no_atp]: "r\<^sup>* \<equiv> (r\<^sup>+)\<^sup>="
  by (simp only: rtrancl_trancl_reflcl)

lemma rtranclp_unfold [nitpick_unfold, no_atp]:
"rtranclp r a b \<equiv> (a = b \<or> tranclp r a b)"
by (rule eq_reflection) (auto dest: rtranclpD)

lemma tranclp_unfold [nitpick_unfold, no_atp]:
"tranclp r a b \<equiv> (a, b) \<in> trancl {(x, y). r x y}"
by (simp add: trancl_def)

lemma [nitpick_simp, no_atp]:
"of_nat n = (if n = 0 then 0 else 1 + of_nat (n - 1))"
by (cases n) auto

definition prod :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set" where
"prod A B = {(a, b). a \<in> A \<and> b \<in> B}"

definition refl' :: "('a \<times> 'a) set \<Rightarrow> bool" where
"refl' r \<equiv> \<forall>x. (x, x) \<in> r"

definition wf' :: "('a \<times> 'a) set \<Rightarrow> bool" where
"wf' r \<equiv> acyclic r \<and> (finite r \<or> unknown)"

definition card' :: "'a set \<Rightarrow> nat" where
"card' A \<equiv> if finite A then length (SOME xs. set xs = A \<and> distinct xs) else 0"

definition setsum' :: "('a \<Rightarrow> 'b\<Colon>comm_monoid_add) \<Rightarrow> 'a set \<Rightarrow> 'b" where
"setsum' f A \<equiv> if finite A then listsum (map f (SOME xs. set xs = A \<and> distinct xs)) else 0"

inductive fold_graph' :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> bool" where
"fold_graph' f z {} z" |
"\<lbrakk>x \<in> A; fold_graph' f z (A - {x}) y\<rbrakk> \<Longrightarrow> fold_graph' f z A (f x y)"

text {*
The following lemmas are not strictly necessary but they help the
\textit{specialize} optimization.
*}

lemma The_psimp [nitpick_psimp, no_atp]:
  "P = (op =) x \<Longrightarrow> The P = x"
  by auto

lemma Eps_psimp [nitpick_psimp, no_atp]:
"\<lbrakk>P x; \<not> P y; Eps P = y\<rbrakk> \<Longrightarrow> Eps P = x"
apply (cases "P (Eps P)")
 apply auto
apply (erule contrapos_np)
by (rule someI)

lemma unit_case_unfold [nitpick_unfold, no_atp]:
"unit_case x u \<equiv> x"
apply (subgoal_tac "u = ()")
 apply (simp only: unit.cases)
by simp

declare unit.cases [nitpick_simp del]

lemma nat_case_unfold [nitpick_unfold, no_atp]:
"nat_case x f n \<equiv> if n = 0 then x else f (n - 1)"
apply (rule eq_reflection)
by (cases n) auto

declare nat.cases [nitpick_simp del]

lemma list_size_simp [nitpick_simp, no_atp]:
"list_size f xs = (if xs = [] then 0
                   else Suc (f (hd xs) + list_size f (tl xs)))"
"size xs = (if xs = [] then 0 else Suc (size (tl xs)))"
by (cases xs) auto

text {*
Auxiliary definitions used to provide an alternative representation for
@{text rat} and @{text real}.
*}

function nat_gcd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
[simp del]: "nat_gcd x y = (if y = 0 then x else nat_gcd y (x mod y))"
by auto
termination
apply (relation "measure (\<lambda>(x, y). x + y + (if y > x then 1 else 0))")
 apply auto
 apply (metis mod_less_divisor xt1(9))
by (metis mod_mod_trivial mod_self nat_neq_iff xt1(10))

definition nat_lcm :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"nat_lcm x y = x * y div (nat_gcd x y)"

definition int_gcd :: "int \<Rightarrow> int \<Rightarrow> int" where
"int_gcd x y = int (nat_gcd (nat (abs x)) (nat (abs y)))"

definition int_lcm :: "int \<Rightarrow> int \<Rightarrow> int" where
"int_lcm x y = int (nat_lcm (nat (abs x)) (nat (abs y)))"

definition Frac :: "int \<times> int \<Rightarrow> bool" where
"Frac \<equiv> \<lambda>(a, b). b > 0 \<and> int_gcd a b = 1"

axiomatization Abs_Frac :: "int \<times> int \<Rightarrow> 'a"
           and Rep_Frac :: "'a \<Rightarrow> int \<times> int"

definition zero_frac :: 'a where
"zero_frac \<equiv> Abs_Frac (0, 1)"

definition one_frac :: 'a where
"one_frac \<equiv> Abs_Frac (1, 1)"

definition num :: "'a \<Rightarrow> int" where
"num \<equiv> fst o Rep_Frac"

definition denom :: "'a \<Rightarrow> int" where
"denom \<equiv> snd o Rep_Frac"

function norm_frac :: "int \<Rightarrow> int \<Rightarrow> int \<times> int" where
[simp del]: "norm_frac a b = (if b < 0 then norm_frac (- a) (- b)
                              else if a = 0 \<or> b = 0 then (0, 1)
                              else let c = int_gcd a b in (a div c, b div c))"
by pat_completeness auto
termination by (relation "measure (\<lambda>(_, b). if b < 0 then 1 else 0)") auto

definition frac :: "int \<Rightarrow> int \<Rightarrow> 'a" where
"frac a b \<equiv> Abs_Frac (norm_frac a b)"

definition plus_frac :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
[nitpick_simp]:
"plus_frac q r = (let d = int_lcm (denom q) (denom r) in
                    frac (num q * (d div denom q) + num r * (d div denom r)) d)"

definition times_frac :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
[nitpick_simp]:
"times_frac q r = frac (num q * num r) (denom q * denom r)"

definition uminus_frac :: "'a \<Rightarrow> 'a" where
"uminus_frac q \<equiv> Abs_Frac (- num q, denom q)"

definition number_of_frac :: "int \<Rightarrow> 'a" where
"number_of_frac n \<equiv> Abs_Frac (n, 1)"

definition inverse_frac :: "'a \<Rightarrow> 'a" where
"inverse_frac q \<equiv> frac (denom q) (num q)"

definition less_frac :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
[nitpick_simp]:
"less_frac q r \<longleftrightarrow> num (plus_frac q (uminus_frac r)) < 0"

definition less_eq_frac :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
[nitpick_simp]:
"less_eq_frac q r \<longleftrightarrow> num (plus_frac q (uminus_frac r)) \<le> 0"

definition of_frac :: "'a \<Rightarrow> 'b\<Colon>{inverse,ring_1}" where
"of_frac q \<equiv> of_int (num q) / of_int (denom q)"

ML_file "Tools/Nitpick/kodkod.ML"
ML_file "Tools/Nitpick/kodkod_sat.ML"
ML_file "Tools/Nitpick/nitpick_util.ML"
ML_file "Tools/Nitpick/nitpick_hol.ML"
ML_file "Tools/Nitpick/nitpick_mono.ML"
ML_file "Tools/Nitpick/nitpick_preproc.ML"
ML_file "Tools/Nitpick/nitpick_scope.ML"
ML_file "Tools/Nitpick/nitpick_peephole.ML"
ML_file "Tools/Nitpick/nitpick_rep.ML"
ML_file "Tools/Nitpick/nitpick_nut.ML"
ML_file "Tools/Nitpick/nitpick_kodkod.ML"
ML_file "Tools/Nitpick/nitpick_model.ML"
ML_file "Tools/Nitpick/nitpick.ML"
ML_file "Tools/Nitpick/nitpick_isar.ML"
ML_file "Tools/Nitpick/nitpick_tests.ML"

setup {*
  Nitpick_Isar.setup #>
  Nitpick_HOL.register_ersatz_global
    [(@{const_name card}, @{const_name card'}),
     (@{const_name setsum}, @{const_name setsum'}),
     (@{const_name fold_graph}, @{const_name fold_graph'}),
     (@{const_name wf}, @{const_name wf'})]
*}

hide_const (open) unknown is_unknown bisim bisim_iterator_max Quot safe_The
    FunBox PairBox Word prod refl' wf' card' setsum'
    fold_graph' nat_gcd nat_lcm int_gcd int_lcm Frac Abs_Frac Rep_Frac zero_frac
    one_frac num denom norm_frac frac plus_frac times_frac uminus_frac
    number_of_frac inverse_frac less_frac less_eq_frac of_frac
hide_type (open) bisim_iterator fun_box pair_box unsigned_bit signed_bit word
hide_fact (open) Ex1_unfold rtrancl_unfold rtranclp_unfold tranclp_unfold
    prod_def refl'_def wf'_def card'_def setsum'_def
    fold_graph'_def The_psimp Eps_psimp unit_case_unfold nat_case_unfold
    list_size_simp nat_gcd_def nat_lcm_def int_gcd_def int_lcm_def Frac_def
    zero_frac_def one_frac_def num_def denom_def norm_frac_def frac_def
    plus_frac_def times_frac_def uminus_frac_def number_of_frac_def
    inverse_frac_def less_frac_def less_eq_frac_def of_frac_def

end
