(*  Title:      HOL/Datatype.thy
    ID:         $Id$
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Datatypes *}

theory Datatype = Datatype_Universe:

subsection {* Representing primitive types *}

rep_datatype bool
  distinct True_not_False False_not_True
  induction bool_induct

declare case_split [cases type: bool]
  -- "prefer plain propositional version"

rep_datatype unit
  induction unit_induct

rep_datatype prod
  inject Pair_eq
  induction prod_induct

rep_datatype sum
  distinct Inl_not_Inr Inr_not_Inl
  inject Inl_eq Inr_eq
  induction sum_induct

ML {*
  val [sum_case_Inl, sum_case_Inr] = thms "sum.cases";
  bind_thm ("sum_case_Inl", sum_case_Inl);
  bind_thm ("sum_case_Inr", sum_case_Inr);
*} -- {* compatibility *}

lemma surjective_sum: "sum_case (%x::'a. f (Inl x)) (%y::'b. f (Inr y)) s = f(s)"
  apply (rule_tac s = s in sumE)
   apply (erule ssubst)
   apply (rule sum_case_Inl)
  apply (erule ssubst)
  apply (rule sum_case_Inr)
  done

lemma sum_case_weak_cong: "s = t ==> sum_case f g s = sum_case f g t"
  -- {* Prevents simplification of @{text f} and @{text g}: much faster. *}
  by (erule arg_cong)

lemma sum_case_inject:
  "sum_case f1 f2 = sum_case g1 g2 ==> (f1 = g1 ==> f2 = g2 ==> P) ==> P"
proof -
  assume a: "sum_case f1 f2 = sum_case g1 g2"
  assume r: "f1 = g1 ==> f2 = g2 ==> P"
  show P
    apply (rule r)
     apply (rule ext)
     apply (cut_tac x = "Inl x" in a [THEN fun_cong])
     apply simp
    apply (rule ext)
    apply (cut_tac x = "Inr x" in a [THEN fun_cong])
    apply simp
    done
qed

constdefs
  Suml :: "('a => 'c) => 'a + 'b => 'c"
  "Suml == (%f. sum_case f arbitrary)"

  Sumr :: "('b => 'c) => 'a + 'b => 'c"
  "Sumr == sum_case arbitrary"

lemma Suml_inject: "Suml f = Suml g ==> f = g"
  by (unfold Suml_def) (erule sum_case_inject)

lemma Sumr_inject: "Sumr f = Sumr g ==> f = g"
  by (unfold Sumr_def) (erule sum_case_inject)


subsection {* Finishing the datatype package setup *}

text {* Belongs to theory @{text Datatype_Universe}; hides popular names. *}
hide const Node Atom Leaf Numb Lim Split Case Suml Sumr
hide type node item


subsection {* Further cases/induct rules for tuples *}

lemma prod_cases3 [case_names fields, cases type]:
    "(!!a b c. y = (a, b, c) ==> P) ==> P"
  apply (cases y)
  apply (case_tac b)
  apply blast
  done

lemma prod_induct3 [case_names fields, induct type]:
    "(!!a b c. P (a, b, c)) ==> P x"
  by (cases x) blast

lemma prod_cases4 [case_names fields, cases type]:
    "(!!a b c d. y = (a, b, c, d) ==> P) ==> P"
  apply (cases y)
  apply (case_tac c)
  apply blast
  done

lemma prod_induct4 [case_names fields, induct type]:
    "(!!a b c d. P (a, b, c, d)) ==> P x"
  by (cases x) blast

lemma prod_cases5 [case_names fields, cases type]:
    "(!!a b c d e. y = (a, b, c, d, e) ==> P) ==> P"
  apply (cases y)
  apply (case_tac d)
  apply blast
  done

lemma prod_induct5 [case_names fields, induct type]:
    "(!!a b c d e. P (a, b, c, d, e)) ==> P x"
  by (cases x) blast

lemma prod_cases6 [case_names fields, cases type]:
    "(!!a b c d e f. y = (a, b, c, d, e, f) ==> P) ==> P"
  apply (cases y)
  apply (case_tac e)
  apply blast
  done

lemma prod_induct6 [case_names fields, induct type]:
    "(!!a b c d e f. P (a, b, c, d, e, f)) ==> P x"
  by (cases x) blast

lemma prod_cases7 [case_names fields, cases type]:
    "(!!a b c d e f g. y = (a, b, c, d, e, f, g) ==> P) ==> P"
  apply (cases y)
  apply (case_tac f)
  apply blast
  done

lemma prod_induct7 [case_names fields, induct type]:
    "(!!a b c d e f g. P (a, b, c, d, e, f, g)) ==> P x"
  by (cases x) blast


subsection {* The option type *}

datatype 'a option = None | Some 'a

lemma not_None_eq [iff]: "(x ~= None) = (EX y. x = Some y)"
  by (induct x) auto

lemma not_Some_eq [iff]: "(ALL y. x ~= Some y) = (x = None)"
  by (induct x) auto

lemma option_caseE:
  "(case x of None => P | Some y => Q y) ==>
    (x = None ==> P ==> R) ==>
    (!!y. x = Some y ==> Q y ==> R) ==> R"
  by (cases x) simp_all


subsubsection {* Operations *}

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

ML_setup {* claset_ref() := claset() addSD2 ("ospec", thm "ospec") *}

lemma elem_o2s [iff]: "(x : o2s xo) = (xo = Some x)"
  by (cases xo) auto

lemma o2s_empty_eq [simp]: "(o2s xo = {}) = (xo = None)"
  by (cases xo) auto


constdefs
  option_map :: "('a => 'b) => ('a option => 'b option)"
  "option_map == %f y. case y of None => None | Some x => Some (f x)"

lemma option_map_None [simp]: "option_map f None = None"
  by (simp add: option_map_def)

lemma option_map_Some [simp]: "option_map f (Some x) = Some (f x)"
  by (simp add: option_map_def)

lemma option_map_eq_Some [iff]:
    "(option_map f xo = Some y) = (EX z. xo = Some z & f z = y)"
  by (simp add: option_map_def split add: option.split)

lemma option_map_o_sum_case [simp]:
    "option_map f o sum_case g h = sum_case (option_map f o g) (option_map f o h)"
  apply (rule ext)
  apply (simp split add: sum.split)
  done

end
