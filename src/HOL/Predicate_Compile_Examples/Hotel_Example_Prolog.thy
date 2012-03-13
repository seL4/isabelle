theory Hotel_Example_Prolog
imports
  Hotel_Example
  "~~/src/HOL/Library/Predicate_Compile_Alternative_Defs"
  "~~/src/HOL/Library/Code_Prolog"
begin

declare Let_def[code_pred_inline]
(*
thm hotel_def
lemma [code_pred_inline]: "insert == (%y A x. y = x | A x)"
by (auto simp add: insert_iff[unfolded mem_def] fun_eq_iff intro!: eq_reflection)

lemma [code_pred_inline]: "(op -) == (%A B x. A x \<and> \<not> B x)"
by (auto simp add: Diff_iff[unfolded mem_def] fun_eq_iff intro!: eq_reflection)
*)

definition issuedp :: "event list => key => bool"
where
  "issuedp evs k = (k \<in> issued evs)"

lemma [code_pred_def]:
  "issuedp [] Key0 = True"
  "issuedp (e # s) k = (issuedp s k \<or> (case e of Check_in g r (k1, k2) => k = k2 | _ => False))"
unfolding issuedp_def issued.simps initk_def
by (auto split: event.split)

definition cardsp
where
 "cardsp s g k = (k \<in> cards s g)"

lemma [code_pred_def]:
  "cardsp [] g k = False"
  "cardsp (e # s) g k = (let C = cardsp s g in case e of Check_in g' r c => if g' = g then k = c \<or> C k else C k | _ => C k)"
unfolding cardsp_def [abs_def] cards.simps by (auto simp add: Let_def split: event.split)

definition
  "isinp evs r g = (g \<in> isin evs r)"

lemma [code_pred_def]:
  "isinp [] r g = False"
  "isinp (e # s) r g =
  (let G = isinp s r
   in case e of Check_in g' r c => G g
    | Enter g' r' c => if r' = r then g = g' \<or> G g else G g
    | Exit g' r' => if r' = r then ((g \<noteq> g') \<and> G g) else G g)"
unfolding isinp_def [abs_def] isin.simps by (auto simp add: Let_def split: event.split)

declare hotel.simps(1)[code_pred_def]
lemma [code_pred_def]:
"hotel (e # s) =
  (hotel s & (case e of Check_in g r (k, k') => k = currk s r & \<not> issuedp s k'
  | Enter g r (k, k') => cardsp s g (k, k') & (roomk s r = k \<or> roomk s r = k')
  | Exit g r => isinp s r g))"
unfolding hotel.simps issuedp_def cardsp_def isinp_def
by (auto split: event.split)

declare List.member_rec[code_pred_def]

lemma [code_pred_def]: "no_Check_in s r = (~ (EX g c. List.member s (Check_in g r c)))"
unfolding no_Check_in_def member_def by auto

lemma [code_pred_def]: "feels_safe s r =
(EX s\<^isub>1 s\<^isub>2 s\<^isub>3 g c c'.
    s =
    s\<^isub>3 @
    [Enter g r c] @ s\<^isub>2 @ [Check_in g r c'] @ s\<^isub>1 &
    no_Check_in (s\<^isub>3 @ s\<^isub>2) r &
    (\<not> (\<exists> g'. isinp (s\<^isub>2 @ [Check_in g r c] @ s\<^isub>1) r g')))"
unfolding feels_safe_def isinp_def by auto

setup {* Code_Prolog.map_code_options (K
  {ensure_groundness = true,
  limit_globally = NONE,
  limited_types = [],
  limited_predicates = [],
  replacing = [],
  manual_reorder = []}) *}

values 40 "{s. hotel s}"

setup {* Context.theory_map (Quickcheck.add_tester ("prolog", (Code_Prolog.active, Code_Prolog.test_goals))) *}

lemma "\<lbrakk> hotel s; isinp s r g \<rbrakk> \<Longrightarrow> owns s r = Some g"
quickcheck[tester = prolog, iterations = 1, expect = counterexample]
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
  "hotel s ==> feels_safe s r ==> isinp s r g ==> owns s r = Some g"
quickcheck[tester = prolog, iterations = 1, expect = no_counterexample]
oops

setup {* Code_Prolog.map_code_options (K 
  {ensure_groundness = true,
   limit_globally = NONE,
   limited_types = [],
   limited_predicates = [(["hotel"], 5)],
   replacing = [(("hotel", "limited_hotel"), "quickcheck")],
   manual_reorder = []}) *}

lemma
  "hotel s ==> feels_safe s r ==> isinp s r g ==> owns s r = Some g"
quickcheck[tester = prolog, iterations = 1, expect = counterexample]
oops

section {* Using a global limit for limiting the execution *} 

text {* A global depth limit of 10 does not suffice to find the counterexample. *}

setup {*
  Code_Prolog.map_code_options (K
  {ensure_groundness = true,
  limit_globally = SOME 10,
  limited_types = [],
  limited_predicates = [],
  replacing = [],
  manual_reorder = []})
*}

lemma
  "hotel s ==> feels_safe s r ==> isinp s r g ==> owns s r = Some g"
quickcheck[tester = prolog, iterations = 1, expect = no_counterexample]
oops

text {* But a global depth limit of 11 does. *}

setup {*
  Code_Prolog.map_code_options (K
  {ensure_groundness = true,
  limit_globally = SOME 11,
  limited_types = [],
  limited_predicates = [],
  replacing = [],
  manual_reorder = []})
*}

lemma
  "hotel s ==> feels_safe s r ==> isinp s r g ==> owns s r = Some g"
quickcheck[tester = prolog, iterations = 1, expect = counterexample]
oops

end