(* Author: Florian Haftmann, TU Muenchen *)

section \<open>A HOL random engine\<close>

theory Random
imports List Groups_List
begin

subsection \<open>Auxiliary functions\<close>

fun log :: "natural \<Rightarrow> natural \<Rightarrow> natural" where
  "log b i = (if b \<le> 1 \<or> i < b then 1 else 1 + log b (i div b))"

definition inc_shift :: "natural \<Rightarrow> natural \<Rightarrow> natural" where
  "inc_shift v k = (if v = k then 1 else k + 1)"

definition minus_shift :: "natural \<Rightarrow> natural \<Rightarrow> natural \<Rightarrow> natural" where
  "minus_shift r k l = (if k < l then r + k - l else k - l)"


subsection \<open>Random seeds\<close>

type_synonym seed = "natural \<times> natural"

primrec "next" :: "seed \<Rightarrow> natural \<times> seed" where
  "next (v, w) = (let
     k =  v div 53668;
     v' = minus_shift 2147483563 ((v mod 53668) * 40014) (k * 12211);
     l =  w div 52774;
     w' = minus_shift 2147483399 ((w mod 52774) * 40692) (l * 3791);
     z =  minus_shift 2147483562 v' (w' + 1) + 1
   in (z, (v', w')))"

definition split_seed :: "seed \<Rightarrow> seed \<times> seed" where
  "split_seed s = (let
     (v, w) = s;
     (v', w') = snd (next s);
     v'' = inc_shift 2147483562 v;
     w'' = inc_shift 2147483398 w
   in ((v'', w'), (v', w'')))"


subsection \<open>Base selectors\<close>

context
  includes state_combinator_syntax
begin

fun iterate :: "natural \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'b \<times> 'a) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<times> 'a" where
  "iterate k f x = (if k = 0 then Pair x else f x \<circ>\<rightarrow> iterate (k - 1) f)"

definition range :: "natural \<Rightarrow> seed \<Rightarrow> natural \<times> seed" where
  "range k = iterate (log 2147483561 k)
      (\<lambda>l. next \<circ>\<rightarrow> (\<lambda>v. Pair (v + l * 2147483561))) 1
    \<circ>\<rightarrow> (\<lambda>v. Pair (v mod k))"

lemma range:
  "k > 0 \<Longrightarrow> fst (range k s) < k"
  by (simp add: range_def split_def less_natural_def del: log.simps iterate.simps)

definition select :: "'a list \<Rightarrow> seed \<Rightarrow> 'a \<times> seed" where
  "select xs = range (natural_of_nat (length xs))
    \<circ>\<rightarrow> (\<lambda>k. Pair (nth xs (nat_of_natural k)))"
     
lemma select:
  assumes "xs \<noteq> []"
  shows "fst (select xs s) \<in> set xs"
proof -
  from assms have "natural_of_nat (length xs) > 0" by (simp add: less_natural_def)
  with range have
    "fst (range (natural_of_nat (length xs)) s) < natural_of_nat (length xs)" by best
  then have
    "nat_of_natural (fst (range (natural_of_nat (length xs)) s)) < length xs" by (simp add: less_natural_def)
  then show ?thesis
    by (simp add: split_beta select_def)
qed

primrec pick :: "(natural \<times> 'a) list \<Rightarrow> natural \<Rightarrow> 'a" where
  "pick (x # xs) i = (if i < fst x then snd x else pick xs (i - fst x))"

lemma pick_member:
  "i < sum_list (map fst xs) \<Longrightarrow> pick xs i \<in> set (map snd xs)"
  by (induct xs arbitrary: i) (simp_all add: less_natural_def)

lemma pick_drop_zero:
  "pick (filter (\<lambda>(k, _). k > 0) xs) = pick xs"
  by (induct xs) (auto simp add: fun_eq_iff less_natural_def minus_natural_def)

lemma pick_same:
  "l < length xs \<Longrightarrow> Random.pick (map (Pair 1) xs) (natural_of_nat l) = nth xs l"
proof (induct xs arbitrary: l)
  case Nil then show ?case by simp
next
  case (Cons x xs) then show ?case by (cases l) (simp_all add: less_natural_def)
qed

definition select_weight :: "(natural \<times> 'a) list \<Rightarrow> seed \<Rightarrow> 'a \<times> seed" where
  "select_weight xs = range (sum_list (map fst xs))
   \<circ>\<rightarrow> (\<lambda>k. Pair (pick xs k))"

lemma select_weight_member:
  assumes "0 < sum_list (map fst xs)"
  shows "fst (select_weight xs s) \<in> set (map snd xs)"
proof -
  from range assms
    have "fst (range (sum_list (map fst xs)) s) < sum_list (map fst xs)" .
  with pick_member
    have "pick xs (fst (range (sum_list (map fst xs)) s)) \<in> set (map snd xs)" .
  then show ?thesis by (simp add: select_weight_def scomp_def split_def) 
qed

lemma select_weight_cons_zero:
  "select_weight ((0, x) # xs) = select_weight xs"
  by (simp add: select_weight_def less_natural_def)

lemma select_weight_drop_zero:
  "select_weight (filter (\<lambda>(k, _). k > 0) xs) = select_weight xs"
proof -
  have "sum_list (map fst [(k, _)\<leftarrow>xs . 0 < k]) = sum_list (map fst xs)"
    by (induct xs) (auto simp add: less_natural_def natural_eq_iff)
  then show ?thesis by (simp only: select_weight_def pick_drop_zero)
qed

lemma select_weight_select:
  assumes "xs \<noteq> []"
  shows "select_weight (map (Pair 1) xs) = select xs"
proof -
  have less: "\<And>s. fst (range (natural_of_nat (length xs)) s) < natural_of_nat (length xs)"
    using assms by (intro range) (simp add: less_natural_def)
  moreover have "sum_list (map fst (map (Pair 1) xs)) = natural_of_nat (length xs)"
    by (induct xs) simp_all
  ultimately show ?thesis
    by (auto simp add: select_weight_def select_def scomp_def split_def
      fun_eq_iff pick_same [symmetric] less_natural_def)
qed

end


subsection \<open>\<open>ML\<close> interface\<close>

code_reflect Random_Engine
  functions range select select_weight

ML \<open>
structure Random_Engine =
struct

open Random_Engine;

type seed = Code_Numeral.natural * Code_Numeral.natural;

local

val seed = Unsynchronized.ref 
  (let
    val now = Time.toMilliseconds (Time.now ());
    val (q, s1) = IntInf.divMod (now, 2147483562);
    val s2 = q mod 2147483398;
  in apply2 Code_Numeral.natural_of_integer (s1 + 1, s2 + 1) end);

in

fun next_seed () =
  let
    val (seed1, seed') = @{code split_seed} (! seed)
    val _ = seed := seed'
  in
    seed1
  end

fun run f =
  let
    val (x, seed') = f (! seed);
    val _ = seed := seed'
  in x end;

end;

end;
\<close>

hide_type (open) seed
hide_const (open) inc_shift minus_shift log "next" split_seed
  iterate range select pick select_weight
hide_fact (open) range_def

end
