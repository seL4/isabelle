(*  Title:      HOL/Types_To_Sets/Types_To_Sets.thy
    Author:     Ondřej Kunčar, TU München
*)

section \<open>From Types to Sets\<close>

text \<open>This theory extends Isabelle/HOL's logic by two new inference rules
  to allow translation of types to sets as described in
  O. Kunčar, A. Popescu: From Types to Sets by Local Type Definitions in Higher-Order Logic
  available at https://www21.in.tum.de/~kuncar/documents/kuncar-popescu-t2s2016-extended.pdf.\<close>

theory Types_To_Sets
  imports Main
begin

subsection \<open>Rules\<close>

text\<open>The following file implements the Local Typedef Rule (LT) and extends the logic by the rule.\<close>
ML_file "local_typedef.ML"

text\<open>The following file implements the Unoverloading Rule (UO) and extends the logic by the rule.\<close>
ML_file "unoverloading.ML"

text\<open>The following file implements a derived rule that internalizes type class annotations.\<close>
ML_file "internalize_sort.ML"

end
