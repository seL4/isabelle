(*  Title:      HOL/Option.thy
    Author:     Folklore
*)

header {* Datatype option *}

theory Option
imports Datatype
begin

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

lemma insert_None_conv_UNIV: "insert None (range Some) = UNIV"
  by (rule set_ext, case_tac x) auto

lemma inj_Some [simp]: "inj_on Some A"
  by (rule inj_onI) simp


subsubsection {* Operations *}

primrec the :: "'a option => 'a" where
"the (Some x) = x"

primrec set :: "'a option => 'a set" where
"set None = {}" |
"set (Some x) = {x}"

lemma ospec [dest]: "(ALL x:set A. P x) ==> A = Some x ==> P x"
  by simp

declaration {* fn _ =>
  Classical.map_cs (fn cs => cs addSD2 ("ospec", thm "ospec"))
*}

lemma elem_set [iff]: "(x : set xo) = (xo = Some x)"
  by (cases xo) auto

lemma set_empty_eq [simp]: "(set xo = {}) = (xo = None)"
  by (cases xo) auto

definition
  map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow> 'b option"
where
  [code del]: "map = (%f y. case y of None => None | Some x => Some (f x))"

lemma option_map_None [simp, code]: "map f None = None"
  by (simp add: map_def)

lemma option_map_Some [simp, code]: "map f (Some x) = Some (f x)"
  by (simp add: map_def)

lemma option_map_is_None [iff]:
    "(map f opt = None) = (opt = None)"
  by (simp add: map_def split add: option.split)

lemma option_map_eq_Some [iff]:
    "(map f xo = Some y) = (EX z. xo = Some z & f z = y)"
  by (simp add: map_def split add: option.split)

lemma option_map_comp:
    "map f (map g opt) = map (f o g) opt"
  by (simp add: map_def split add: option.split)

lemma option_map_o_sum_case [simp]:
    "map f o sum_case g h = sum_case (map f o g) (map f o h)"
  by (rule ext) (simp split: sum.split)


hide (open) const set map

subsubsection {* Code generator setup *}

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

code_const "eq_class.eq \<Colon> 'a\<Colon>eq option \<Rightarrow> 'a option \<Rightarrow> bool"
  (Haskell infixl 4 "==")

code_reserved SML
  option NONE SOME

code_reserved OCaml
  option None Some

end
