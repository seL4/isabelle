(*  Title:      HOL/ex/Sorting_Algorithms_Examples.thy
    Author:     Florian Haftmann, TU Muenchen
*)

theory Sorting_Algorithms_Examples
  imports Main "HOL-Library.Sorting_Algorithms"
begin

subsection \<open>Evaluation examples\<close>

definition int_abs_reversed :: "int comparator"
  where "int_abs_reversed = key abs (reversed default)"

definition example_1 :: "int list"
  where "example_1 = [65, 1705, -2322, 734, 4, (-17::int)]"

definition example_2 :: "int list"
  where "example_2 = [-3000..3000]"

ML \<open>
local

  val term_of_int_list = HOLogic.mk_list \<^typ>\<open>int\<close>
    o map (HOLogic.mk_number \<^typ>\<open>int\<close> o @{code integer_of_int});

  fun raw_sort (ctxt, ct, ks) = Thm.mk_binop \<^cterm>\<open>Pure.eq :: int list \<Rightarrow> int list \<Rightarrow> prop\<close>
    ct (Thm.cterm_of ctxt (term_of_int_list ks));

  val (_, sort_oracle) = Context.>>> (Context.map_theory_result
    (Thm.add_oracle (\<^binding>\<open>sort\<close>, raw_sort)));

in

  val sort_int_abs_reversed_conv = @{computation_conv "int list" terms: int_abs_reversed
    "sort :: int comparator \<Rightarrow> _"
    "quicksort :: int comparator \<Rightarrow> _"
    "mergesort :: int comparator \<Rightarrow> _"
    example_1 example_2
  } (fn ctxt => fn ct => fn ks => sort_oracle (ctxt, ks, ct))

end
\<close>

declare [[code_timing]]

ML_val \<open>sort_int_abs_reversed_conv \<^context>
  \<^cterm>\<open>sort int_abs_reversed example_1\<close>\<close>

ML_val \<open>sort_int_abs_reversed_conv \<^context>
  \<^cterm>\<open>quicksort int_abs_reversed example_1\<close>\<close>

ML_val \<open>sort_int_abs_reversed_conv \<^context>
  \<^cterm>\<open>mergesort int_abs_reversed example_1\<close>\<close>

ML_val \<open>sort_int_abs_reversed_conv \<^context>
  \<^cterm>\<open>sort int_abs_reversed example_2\<close>\<close>

ML_val \<open>sort_int_abs_reversed_conv \<^context>
  \<^cterm>\<open>quicksort int_abs_reversed example_2\<close>\<close>

ML_val \<open>sort_int_abs_reversed_conv \<^context>
  \<^cterm>\<open>mergesort int_abs_reversed example_2\<close>\<close>

end
