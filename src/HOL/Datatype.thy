(*  Title:      HOL/Datatype.thy
    ID:         $Id$
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Final stage of datatype setup *}

theory Datatype = Datatype_Universe:

text {* Belongs to theory @{text Datatype_Universe}; hides popular names. *}
hide const Node Atom Leaf Numb Lim Funs Split Case
hide type node item


subsection {* Representing primitive types *}

rep_datatype bool
  distinct True_not_False False_not_True
  induction bool_induct

declare case_split [cases type: bool]
  -- "prefer plain propositional version"

rep_datatype sum
  distinct Inl_not_Inr Inr_not_Inl
  inject Inl_eq Inr_eq
  induction sum_induct

rep_datatype unit
  induction unit_induct

rep_datatype prod
  inject Pair_eq
  induction prod_induct

text {* Further cases/induct rules for 3--7 tuples. *}

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

end
