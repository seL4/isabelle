theory List_Examples
imports
  Main
  "HOL-Library.Predicate_Compile_Quickcheck"
  "HOL-Library.Code_Prolog"
begin

setup \<open>
  Context.theory_map
    (Quickcheck.add_tester ("prolog", (Code_Prolog.active, Code_Prolog.test_goals)))
\<close>

setup \<open>Code_Prolog.map_code_options (K 
  {ensure_groundness = true,
   limit_globally = NONE,
   limited_types = [(\<^typ>\<open>nat\<close>, 2), (\<^typ>\<open>nat list\<close>, 4)],
   limited_predicates = [(["appendP"], 4), (["revP"], 4)],
   replacing =
     [(("appendP", "limited_appendP"), "quickcheck"),
      (("revP", "limited_revP"), "quickcheck"),
      (("appendP", "limited_appendP"), "lim_revP")],
   manual_reorder = []})\<close>

lemma "(xs :: nat list) = ys @ ys --> rev xs = xs"
quickcheck[tester = random, iterations = 10000]
quickcheck[tester = smart_exhaustive, iterations = 1, expect = counterexample]
quickcheck[tester = prolog, expect = counterexample]
oops

end
