theory Hotel_Example_Prolog
imports
  Hotel_Example
  "HOL-Library.Predicate_Compile_Alternative_Defs"
  "HOL-Library.Code_Prolog"
begin

declare Let_def[code_pred_inline]
(*
thm hotel_def
lemma [code_pred_inline]: "insert == (%y A x. y = x | A x)"
by (auto simp add: insert_iff[unfolded mem_def] fun_eq_iff intro!: eq_reflection)

lemma [code_pred_inline]: "(-) == (%A B x. A x \<and> \<not> B x)"
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
  "cardsp (e # s) g k =
    (let C = cardsp s g
     in case e of Check_in g' r c => if g' = g then k = c \<or> C k else C k | _ => C k)"
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

declare List.member_code [code_pred_def]

lemma [code_pred_def]: "no_Check_in s r = (\<not> (\<exists>g c. List.member s (Check_in g r c)))"
  by (simp add: no_Check_in_def)

lemma [code_pred_def]: "feels_safe s r =
(\<exists>s\<^sub>1 s\<^sub>2 s\<^sub>3 g c c'.
    s =
    s\<^sub>3 @
    [Enter g r c] @ s\<^sub>2 @ [Check_in g r c'] @ s\<^sub>1 &
    no_Check_in (s\<^sub>3 @ s\<^sub>2) r &
    (\<not> (\<exists> g'. isinp (s\<^sub>2 @ [Check_in g r c] @ s\<^sub>1) r g')))"
unfolding feels_safe_def isinp_def by auto

setup \<open>Code_Prolog.map_code_options (K
  {ensure_groundness = true,
  limit_globally = NONE,
  limited_types = [],
  limited_predicates = [],
  replacing = [],
  manual_reorder = []})\<close>

values_prolog 40 "{s. hotel s}"

setup \<open>
  Context.theory_map
    (Quickcheck.add_tester ("prolog", (Code_Prolog.active, Code_Prolog.test_goals)))
\<close>

lemma "\<lbrakk> hotel s; isinp s r g \<rbrakk> \<Longrightarrow> owns s r = Some g"
quickcheck[tester = prolog, iterations = 1, expect = counterexample]
oops

section \<open>Manual setup to find the counterexample\<close>

setup \<open>Code_Prolog.map_code_options (K 
  {ensure_groundness = true,
   limit_globally = NONE,
   limited_types = [],
   limited_predicates = [(["hotel"], 4)],
   replacing = [(("hotel", "limited_hotel"), "quickcheck")],
   manual_reorder = []})\<close>

lemma
  "hotel s ==> feels_safe s r ==> isinp s r g ==> owns s r = Some g"
quickcheck[tester = prolog, iterations = 1, expect = no_counterexample]
oops

setup \<open>Code_Prolog.map_code_options (K 
  {ensure_groundness = true,
   limit_globally = NONE,
   limited_types = [],
   limited_predicates = [(["hotel"], 5)],
   replacing = [(("hotel", "limited_hotel"), "quickcheck")],
   manual_reorder = []})\<close>

lemma
  "hotel s ==> feels_safe s r ==> isinp s r g ==> owns s r = Some g"
quickcheck[tester = prolog, iterations = 1, expect = counterexample]
oops

section \<open>Using a global limit for limiting the execution\<close> 

text \<open>A global depth limit of 10 does not suffice to find the counterexample.\<close>

setup \<open>
  Code_Prolog.map_code_options (K
  {ensure_groundness = true,
  limit_globally = SOME 10,
  limited_types = [],
  limited_predicates = [],
  replacing = [],
  manual_reorder = []})
\<close>

lemma
  "hotel s ==> feels_safe s r ==> isinp s r g ==> owns s r = Some g"
quickcheck[tester = prolog, iterations = 1, expect = no_counterexample]
oops

text \<open>But a global depth limit of 11 does.\<close>

setup \<open>
  Code_Prolog.map_code_options (K
  {ensure_groundness = true,
  limit_globally = SOME 11,
  limited_types = [],
  limited_predicates = [],
  replacing = [],
  manual_reorder = []})
\<close>

lemma
  "hotel s ==> feels_safe s r ==> isinp s r g ==> owns s r = Some g"
quickcheck[tester = prolog, iterations = 1, expect = counterexample]
oops

end
