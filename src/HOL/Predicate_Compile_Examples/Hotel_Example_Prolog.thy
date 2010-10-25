theory Hotel_Example_Prolog
imports Hotel_Example Predicate_Compile_Alternative_Defs Code_Prolog
begin

declare Let_def[code_pred_inline]

lemma [code_pred_inline]: "insert == (%y A x. y = x | A x)"
by (auto simp add: insert_iff[unfolded mem_def] fun_eq_iff intro!: eq_reflection)

lemma [code_pred_inline]: "(op -) == (%A B x. A x \<and> \<not> B x)"
by (auto simp add: Diff_iff[unfolded mem_def] fun_eq_iff intro!: eq_reflection)

setup {* Code_Prolog.map_code_options (K
  {ensure_groundness = true,
  limit_globally = NONE,
  limited_types = [],
  limited_predicates = [],
  replacing = [],
  manual_reorder = []}) *}

values 40 "{s. hotel s}"

setup {* Context.theory_map (Quickcheck.add_generator ("prolog", Code_Prolog.quickcheck)) *}

lemma "\<lbrakk> hotel s; g \<in> isin s r \<rbrakk> \<Longrightarrow> owns s r = Some g"
quickcheck[generator = code, iterations = 10000, report]
quickcheck[generator = prolog, iterations = 1, expect = counterexample]
oops

section {* Manual setup to find the counterexample *}

setup {* Code_Prolog.map_code_options (K 
  {ensure_groundness = true,
   limit_globally = NONE,
   limited_types = [],
   limited_predicates = [(["hotel"], 4)],
   replacing = [(("hotel", "limited_hotel"), "quickcheck")],
   manual_reorder = []}) *}

lemma
  "hotel s ==> feels_safe s r ==> g \<in> isin s r ==> owns s r = Some g"
quickcheck[generator = prolog, iterations = 1, expect = no_counterexample]
oops

setup {* Code_Prolog.map_code_options (K 
  {ensure_groundness = true,
   limit_globally = NONE,
   limited_types = [],
   limited_predicates = [(["hotel"], 5)],
   replacing = [(("hotel", "limited_hotel"), "quickcheck")],
   manual_reorder = []}) *}

lemma
  "hotel s ==> feels_safe s r ==> g \<in> isin s r ==> owns s r = Some g"
quickcheck[generator = prolog, iterations = 1, expect = counterexample]
oops

section {* Simulating a global depth limit manually by limiting all predicates *}

setup {*
  Code_Prolog.map_code_options (K
  {ensure_groundness = true,
  limit_globally = NONE,
  limited_types = [],
  limited_predicates = [(["feelssafe", "feelssafeaux", "noCheckin", "noCheckinaux", "appendP", "ownsP", "hotel", "hotelaux", "hotelauxaux", "roomkP", "issued", "currkP", "initkP",
    "cards", "cardsauxauxaux", "cardsauxaux", "cardsaux", "isin", "isinauxauxa", "isinauxauxaux", "isinauxaux", "isinaux", "set"], 12)],
  replacing = [(("hotel", "limited_hotel"), "quickcheck"), (("feelssafe", "limited_feelssafe"), "quickcheck"), (("isin", "limited_isin"), "quickcheck")],
  manual_reorder = []})
*}

lemma
  "hotel s ==> feels_safe s r ==> g \<in> isin s r ==> owns s r = Some g"
quickcheck[generator = prolog, iterations = 1, expect = no_counterexample]
oops

setup {*
  Code_Prolog.map_code_options (K
  {ensure_groundness = true,
  limit_globally = NONE,
  limited_types = [],
  limited_predicates = [(["feelssafe", "feelssafeaux", "noCheckin", "noCheckinaux", "appendP", "ownsP", "hotel", "hotelaux", "hotelauxaux", "roomkP", "issued", "currkP", "initkP",
    "cards", "cardsauxauxaux", "cardsauxaux", "cardsaux", "isin", "isinauxauxa", "isinauxauxaux", "isinauxaux", "isinaux", "set"], 13)],
  replacing = [(("hotel", "limited_hotel"), "quickcheck"), (("feelssafe", "limited_feelssafe"), "quickcheck"), (("isin", "limited_isin"), "quickcheck")],
  manual_reorder = []})
*}

lemma
  "hotel s ==> feels_safe s r ==> g \<in> isin s r ==> owns s r = Some g"
quickcheck[generator = prolog, iterations = 1, expect = counterexample]
oops

section {* Using a global limit for limiting the execution *} 

text {* A global depth limit of 13 does not suffice to find the counterexample. *}

setup {*
  Code_Prolog.map_code_options (K
  {ensure_groundness = true,
  limit_globally = SOME 13,
  limited_types = [],
  limited_predicates = [],
  replacing = [],
  manual_reorder = []})
*}

lemma
  "hotel s ==> feels_safe s r ==> g \<in> isin s r ==> owns s r = Some g"
quickcheck[generator = prolog, iterations = 1, expect = no_counterexample]
oops

text {* But a global depth limit of 14 does. *}

setup {*
  Code_Prolog.map_code_options (K
  {ensure_groundness = true,
  limit_globally = SOME 14,
  limited_types = [],
  limited_predicates = [],
  replacing = [],
  manual_reorder = []})
*}

lemma
  "hotel s ==> feels_safe s r ==> g \<in> isin s r ==> owns s r = Some g"
quickcheck[generator = prolog, iterations = 1, expect = counterexample]
oops

end