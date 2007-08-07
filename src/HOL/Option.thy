(*  Title:      HOL/Datatype.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen
    Author:     Florian Haftmann, TU Muenchen
*)

header {* The option datatype *}

theory Option
imports Datatype
begin

subsection {* Type declaration *}

datatype 'a option = None | Some 'a

lemma not_None_eq [iff]: "(x ~= None) = (EX y. x = Some y)"
  by (induct x) auto

lemma not_Some_eq [iff]: "(ALL y. x ~= Some y) = (x = None)"
  by (induct x) auto

text{*Although it may appear that both of these equalities are helpful
only when applied to assumptions, in practice it seems better to give
them the uniform iff attribute. *}

lemma option_caseE:
  assumes c: "(case x of None => P | Some y => Q y)"
  obtains
    (None) "x = None" and P
  | (Some) y where "x = Some y" and "Q y"
  using c by (cases x) simp_all


subsection {* Operations *}

consts
  the :: "'a option => 'a"
primrec
  "the (Some x) = x"

consts
  o2s :: "'a option => 'a set"
primrec
  "o2s None = {}"
  "o2s (Some x) = {x}"

lemma ospec [dest]: "(ALL x:o2s A. P x) ==> A = Some x ==> P x"
  by simp

ML_setup {* change_claset (fn cs => cs addSD2 ("ospec", thm "ospec")) *}

lemma elem_o2s [iff]: "(x : o2s xo) = (xo = Some x)"
  by (cases xo) auto

lemma o2s_empty_eq [simp]: "(o2s xo = {}) = (xo = None)"
  by (cases xo) auto


constdefs
  option_map :: "('a => 'b) => ('a option => 'b option)"
  [code func del]: "option_map == %f y. case y of None => None | Some x => Some (f x)"

lemma option_map_None [simp, code]: "option_map f None = None"
  by (simp add: option_map_def)

lemma option_map_Some [simp, code]: "option_map f (Some x) = Some (f x)"
  by (simp add: option_map_def)

lemma option_map_is_None [iff]:
    "(option_map f opt = None) = (opt = None)"
  by (simp add: option_map_def split add: option.split)

lemma option_map_eq_Some [iff]:
    "(option_map f xo = Some y) = (EX z. xo = Some z & f z = y)"
  by (simp add: option_map_def split add: option.split)

lemma option_map_comp:
    "option_map f (option_map g opt) = option_map (f o g) opt"
  by (simp add: option_map_def split add: option.split)

lemma option_map_o_sum_case [simp]:
    "option_map f o sum_case g h = sum_case (option_map f o g) (option_map f o h)"
  by (rule ext) (simp split: sum.split)


subsection {* Code generator setup *}

definition
  is_none :: "'a option \<Rightarrow> bool" where
  is_none_none [code post, symmetric, code inline]: "is_none x \<longleftrightarrow> x = None"

lemma is_none_code [code]:
  shows "is_none None \<longleftrightarrow> True"
    and "is_none (Some x) \<longleftrightarrow> False"
  unfolding is_none_none [symmetric] by simp_all

hide (open) const is_none

code_type option
  (SML "_ option")
  (OCaml "_ option")
  (Haskell "Maybe _")

code_const None and Some
  (SML "NONE" and "SOME")
  (OCaml "None" and "Some _")
  (Haskell "Nothing" and "Just")

code_instance option :: eq
  (Haskell -)

code_const "op = \<Colon> 'a\<Colon>eq option \<Rightarrow> 'a option \<Rightarrow> bool"
  (Haskell infixl 4 "==")

code_reserved SML
  option NONE SOME

code_reserved OCaml
  option None Some

end
