(* Author: Tobias Nipkow *)

section \<open>Time Functions in Locales --- An Example\<close>

theory Time_Locale_Example
imports
  "HOL-Library.Time_Functions"
  "HOL-Library.AList"
  Map_Specs
begin

text \<open>If you want to reason about the time complexity of functions in a locale,
you need to parameterize the locale with time functions for all functions that are utilized.
More precisely, if you are in a locale parameterized by some function \<open>f\<close>
and you define a function \<open>g\<close> that uses \<open>f\<close>, and you want to define \<open>T_g\<close>, it will
depend on \<open>T_f\<close>, which you have to make an additional parameter of the locale.
Only then will \<open>time_fun g\<close> work. Below we show a realistic example.\<close>


subsection \<open>Basic Time Functions\<close>

time_fun AList.update

text \<open>\<open>time_fun\<close> needs uncurried defining equations\<close>
lemma
   map_of_simps': "map_of [] (x::'a) = (None :: 'b option)"
  "map_of ((a::'a,b::'b)#ps) x = (if x=a then Some b else map_of ps x)"
by auto

time_fun map_of equations map_of_simps'

lemma T_map_ub: "T_map_of ps a \<le> length ps + 1"
by(induction ps) auto

lemma T_update_ub: "T_update a b ps \<le> length ps + 1"
by(induction ps) auto

lemma length_AList_update_ub: "length (AList.update a b ps) \<le> length ps + 1"
by(induction ps) auto


subsection \<open>Locale\<close>

text \<open>Counting the elements in a list by means of a map
that associates elements with their multiplicities in the list, like a `histogram'.
The locale is parameterized with the map ADT and the timing functions for \<open>lookup\<close> and \<open>update\<close>.\<close>

locale Count_List = Map where update = update for update :: "'a \<Rightarrow> nat \<Rightarrow> 'm \<Rightarrow> 'm" +
fixes T_lookup :: "'m \<Rightarrow> 'a \<Rightarrow> nat"
and T_update :: "'a \<Rightarrow> nat \<Rightarrow> 'm \<Rightarrow> nat"
begin

definition lookup_nat :: "'m \<Rightarrow> 'a \<Rightarrow> nat" where
"lookup_nat m x = (case lookup m x of None \<Rightarrow> 0 | Some n \<Rightarrow> n)"

time_definition lookup_nat

fun count :: "'m \<Rightarrow> 'a list \<Rightarrow> 'm" where
"count m [] = m" |
"count m (x#xs) = count (update x (lookup_nat m x + 1) m) xs"

time_fun count

end


subsection \<open>Interpretation\<close>

text \<open>Interpretation of \<open>Count_List\<close> with association lists as maps.\<close>

lemma map_of_AList_update: "map_of (AList.update a b ps) = ((map_of ps)(a \<mapsto> b))"
by(induction ps) auto

lemma map_of_AList_delete: "map_of (AList.delete a ps) = (map_of ps)(a := None)"
by(induction ps) auto

global_interpretation CL: Count_List
where empty = "[]" and lookup = map_of
and update = AList.update and delete = AList.delete and invar = "\<lambda>_. True"
and T_lookup = T_map_of and T_update = T_update
defines CL_count = CL.count and CL_T_count = CL.T_count
proof (standard, goal_cases)
  case 1
  show ?case by (rule ext) simp
next
  case (2 m a b)
  show ?case by (rule map_of_AList_update)
next
  case (3 m a)
  show ?case by (rule map_of_AList_delete)
next
  case 4
  show ?case by(rule TrueI)
next
  case (5 m a b)
  show ?case by(rule TrueI)
next
  case (6 m a)
  show ?case by(rule TrueI)
qed


subsection \<open>Complexity Proof\<close>

lemma "CL.T_count ps xs \<le> 2 * length xs * (length xs + length ps + 1) + 1"
proof(induction xs arbitrary: ps)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  let ?lps' = "length ps + 1"
  let ?na' = "CL.lookup_nat ps a + 1"
  let ?ps' = "AList.update a ?na' ps"
  have "CL_T_count ps (a # xs) =
        T_map_of ps a + T_update a ?na' ps + CL_T_count (AList.update a ?na' ps) xs + 1"
    by simp
  also have "\<dots> \<le> 2 * ?lps' + CL_T_count ?ps' xs + 1"
    using T_map_ub T_update_ub add_mono by (fastforce simp: mult_2)
  also have "\<dots> \<le> 2 * ?lps' + 2 * length xs * (length xs + length ?ps' + 1) + 1 + 1"
    using Cons.IH by (metis (no_types, lifting) add.assoc add_mono_thms_linordered_semiring(3)
        nat_add_left_cancel_le)
  also have "\<dots> \<le> 2 * ?lps' + 2 * length xs * (length xs + ?lps' + 1) + 1 + 1"
    using length_AList_update_ub
    by (metis add_mono_thms_linordered_semiring(2) add_right_mono mult_le_mono2)
  also have "\<dots> \<le> 2 * length (a # xs) * (length (a # xs) + length ps + 1) + 1"
    by (auto simp: algebra_simps)
  finally show ?case .
qed

end
