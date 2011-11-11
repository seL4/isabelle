theory List_Examples
imports
  Main
  "~~/src/HOL/Library/Predicate_Compile_Quickcheck"
  "~~/src/HOL/Library/Code_Prolog"
begin

setup {* Context.theory_map (Quickcheck.add_tester ("prolog", (Code_Prolog.active, Code_Prolog.test_goals))) *}

setup {* Code_Prolog.map_code_options (K 
  {ensure_groundness = true,
   limit_globally = NONE,
   limited_types = [(@{typ nat}, 2), (@{typ "nat list"}, 4)],
   limited_predicates = [(["appendP"], 4), (["revP"], 4)],
   replacing =
     [(("appendP", "limited_appendP"), "quickcheck"),
      (("revP", "limited_revP"), "quickcheck"),
      (("appendP", "limited_appendP"), "lim_revP")],
   manual_reorder = []}) *}

lemma "(xs :: nat list) = ys @ ys --> rev xs = xs"
quickcheck[tester = random, iterations = 10000]
quickcheck[tester = smart_exhaustive, iterations = 1, expect = counterexample]
quickcheck[tester = prolog, expect = counterexample]
oops

end