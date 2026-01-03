(*  Title:      HOL/Nitpick.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009, 2010

Nitpick: Yet another counterexample generator for Isabelle/HOL.
*)

section \<open>Nitpick: Yet Another Counterexample Generator for Isabelle/HOL\<close>

theory Nitpick
imports Record GCD
keywords
  "nitpick" :: diag and
  "nitpick_params" :: thy_decl
begin

datatype (plugins only: extraction) (dead 'a, dead 'b) fun_box = FunBox "'a \<Rightarrow> 'b"
datatype (plugins only: extraction) (dead 'a, dead 'b) pair_box = PairBox 'a 'b
datatype (plugins only: extraction) (dead 'a) word = Word "'a set"

typedecl bisim_iterator
typedecl unsigned_bit
typedecl signed_bit

consts
  unknown :: 'a
  is_unknown :: "'a \<Rightarrow> bool"
  bisim :: "bisim_iterator \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  bisim_iterator_max :: bisim_iterator
  Quot :: "'a \<Rightarrow> 'b"
  safe_The :: "('a \<Rightarrow> bool) \<Rightarrow> 'a"

text \<open>
Alternative definitions.
\<close>

lemma Ex1_unfold[nitpick_unfold]: "Ex1 P \<equiv> \<exists>x. {x. P x} = {x}"
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

lemma rtrancl_unfold[nitpick_unfold]: "r\<^sup>* \<equiv> (r\<^sup>+)\<^sup>="
  by (simp only: rtrancl_trancl_reflcl)

lemma rtranclp_unfold[nitpick_unfold]: "rtranclp r a b \<equiv> (a = b \<or> tranclp r a b)"
  by (rule eq_reflection) (auto dest: rtranclpD)

lemma tranclp_unfold[nitpick_unfold]:
  "tranclp r a b \<equiv> (a, b) \<in> trancl {(x, y). r x y}"
  by (simp add: trancl_def)

lemma [nitpick_simp]:
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

definition sum' :: "('a \<Rightarrow> 'b::comm_monoid_add) \<Rightarrow> 'a set \<Rightarrow> 'b" where
  "sum' f A \<equiv> if finite A then sum_list (map f (SOME xs. set xs = A \<and> distinct xs)) else 0"

inductive fold_graph' :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> bool" where
  "fold_graph' f z {} z" |
  "\<lbrakk>x \<in> A; fold_graph' f z (A - {x}) y\<rbrakk> \<Longrightarrow> fold_graph' f z A (f x y)"

text \<open>
The following lemmas are not strictly necessary but they help the
\textit{specialize} optimization.
\<close>

lemma The_psimp[nitpick_psimp]: "P = (=) x \<Longrightarrow> The P = x"
  by auto

lemma Eps_psimp[nitpick_psimp]:
  "\<lbrakk>P x; \<not> P y; Eps P = y\<rbrakk> \<Longrightarrow> Eps P = x"
  apply (cases "P (Eps P)")
   apply auto
  apply (erule contrapos_np)
  by (rule someI)

lemma case_unit_unfold[nitpick_unfold]:
  "case_unit x u \<equiv> x"
  apply (subgoal_tac "u = ()")
   apply (simp only: unit.case)
  by simp

declare unit.case[nitpick_simp del]

lemma case_nat_unfold[nitpick_unfold]:
  "case_nat x f n \<equiv> if n = 0 then x else f (n - 1)"
  apply (rule eq_reflection)
  by (cases n) auto

declare nat.case[nitpick_simp del]

lemma size_list_simp[nitpick_simp]:
  "size_list f xs = (if xs = [] then 0 else Suc (f (hd xs) + size_list f (tl xs)))"
  "size xs = (if xs = [] then 0 else Suc (size (tl xs)))"
  by (cases xs) auto

text \<open>
Auxiliary definitions used to provide an alternative representation for
\<open>rat\<close> and \<open>real\<close>.
\<close>

fun nat_gcd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "nat_gcd x y = (if y = 0 then x else nat_gcd y (x mod y))"
  
declare nat_gcd.simps [simp del]

definition nat_lcm :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "nat_lcm x y = x * y div (nat_gcd x y)"

lemma gcd_eq_nitpick_gcd [nitpick_unfold]:
  "gcd x y = Nitpick.nat_gcd x y"
  by (induct x y rule: nat_gcd.induct)
    (simp add: gcd_nat.simps Nitpick.nat_gcd.simps)

lemma lcm_eq_nitpick_lcm [nitpick_unfold]:
  "lcm x y = Nitpick.nat_lcm x y"
  by (simp only: lcm_nat_def Nitpick.nat_lcm_def gcd_eq_nitpick_gcd)

definition Frac :: "int \<times> int \<Rightarrow> bool" where
  "Frac \<equiv> \<lambda>(a, b). b > 0 \<and> coprime a b"

consts
  Abs_Frac :: "int \<times> int \<Rightarrow> 'a"
  Rep_Frac :: "'a \<Rightarrow> int \<times> int"

definition zero_frac :: 'a where
  "zero_frac \<equiv> Abs_Frac (0, 1)"

definition one_frac :: 'a where
  "one_frac \<equiv> Abs_Frac (1, 1)"

definition num :: "'a \<Rightarrow> int" where
  "num \<equiv> fst \<circ> Rep_Frac"

definition denom :: "'a \<Rightarrow> int" where
  "denom \<equiv> snd \<circ> Rep_Frac"

function norm_frac :: "int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "norm_frac a b =
    (if b < 0 then norm_frac (- a) (- b)
     else if a = 0 \<or> b = 0 then (0, 1)
     else let c = gcd a b in (a div c, b div c))"
  by pat_completeness auto
  termination by (relation "measure (\<lambda>(_, b). if b < 0 then 1 else 0)") auto

declare norm_frac.simps[simp del]

definition frac :: "int \<Rightarrow> int \<Rightarrow> 'a" where
  "frac a b \<equiv> Abs_Frac (norm_frac a b)"

definition plus_frac :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  [nitpick_simp]: "plus_frac q r = (let d = lcm (denom q) (denom r) in
    frac (num q * (d div denom q) + num r * (d div denom r)) d)"

definition times_frac :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  [nitpick_simp]: "times_frac q r = frac (num q * num r) (denom q * denom r)"

definition uminus_frac :: "'a \<Rightarrow> 'a" where
  "uminus_frac q \<equiv> Abs_Frac (- num q, denom q)"

definition number_of_frac :: "int \<Rightarrow> 'a" where
  "number_of_frac n \<equiv> Abs_Frac (n, 1)"

definition inverse_frac :: "'a \<Rightarrow> 'a" where
  "inverse_frac q \<equiv> frac (denom q) (num q)"

definition less_frac :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  [nitpick_simp]: "less_frac q r \<longleftrightarrow> num (plus_frac q (uminus_frac r)) < 0"

definition less_eq_frac :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  [nitpick_simp]: "less_eq_frac q r \<longleftrightarrow> num (plus_frac q (uminus_frac r)) \<le> 0"

definition of_frac :: "'a \<Rightarrow> 'b::{inverse,ring_1}" where
  "of_frac q \<equiv> of_int (num q) / of_int (denom q)"

axiomatization wf_wfrec :: "('a \<times> 'a) set \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"

definition wf_wfrec' :: "('a \<times> 'a) set \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
  [nitpick_simp]: "wf_wfrec' R F x = F (Wfrec.cut (wf_wfrec R F) R x) x"

definition wfrec' ::  "('a \<times> 'a) set \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
  "wfrec' R F x \<equiv> if wf R then wf_wfrec' R F x else THE y. wfrec_rel R (\<lambda>f x. F (Wfrec.cut f R x) x) x y"

ML_file \<open>Tools/Nitpick/kodkod.ML\<close>
ML_file \<open>Tools/Nitpick/kodkod_sat.ML\<close>
ML_file \<open>Tools/Nitpick/nitpick_util.ML\<close>
ML_file \<open>Tools/Nitpick/nitpick_hol.ML\<close>
ML_file \<open>Tools/Nitpick/nitpick_mono.ML\<close>
ML_file \<open>Tools/Nitpick/nitpick_preproc.ML\<close>
ML_file \<open>Tools/Nitpick/nitpick_scope.ML\<close>
ML_file \<open>Tools/Nitpick/nitpick_peephole.ML\<close>
ML_file \<open>Tools/Nitpick/nitpick_rep.ML\<close>
ML_file \<open>Tools/Nitpick/nitpick_nut.ML\<close>
ML_file \<open>Tools/Nitpick/nitpick_kodkod.ML\<close>
ML_file \<open>Tools/Nitpick/nitpick_model.ML\<close>
ML_file \<open>Tools/Nitpick/nitpick.ML\<close>
ML_file \<open>Tools/Nitpick/nitpick_commands.ML\<close>
ML_file \<open>Tools/Nitpick/nitpick_tests.ML\<close>

setup \<open>
  Nitpick_HOL.register_ersatz_global
    [(\<^const_name>\<open>card\<close>, \<^const_name>\<open>card'\<close>),
     (\<^const_name>\<open>sum\<close>, \<^const_name>\<open>sum'\<close>),
     (\<^const_name>\<open>fold_graph\<close>, \<^const_name>\<open>fold_graph'\<close>),
     (\<^const_abbrev>\<open>wf\<close>, \<^const_name>\<open>wf'\<close>),
     (\<^const_name>\<open>wf_wfrec\<close>, \<^const_name>\<open>wf_wfrec'\<close>),
     (\<^const_name>\<open>wfrec\<close>, \<^const_name>\<open>wfrec'\<close>)]
\<close>

hide_const (open) unknown is_unknown bisim bisim_iterator_max Quot safe_The FunBox PairBox Word prod
  refl' wf' card' sum' fold_graph' nat_gcd nat_lcm Frac Abs_Frac Rep_Frac
  zero_frac one_frac num denom norm_frac frac plus_frac times_frac uminus_frac number_of_frac
  inverse_frac less_frac less_eq_frac of_frac wf_wfrec wf_wfrec wfrec'

hide_type (open) bisim_iterator fun_box pair_box unsigned_bit signed_bit word

hide_fact (open) Ex1_unfold rtrancl_unfold rtranclp_unfold tranclp_unfold prod_def refl'_def wf'_def
  card'_def sum'_def The_psimp Eps_psimp case_unit_unfold case_nat_unfold
  size_list_simp nat_lcm_def Frac_def zero_frac_def one_frac_def
  num_def denom_def frac_def plus_frac_def times_frac_def uminus_frac_def
  number_of_frac_def inverse_frac_def less_frac_def less_eq_frac_def of_frac_def wf_wfrec'_def
  wfrec'_def

end
