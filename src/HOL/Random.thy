
(* Author: Florian Haftmann, TU Muenchen *)

header {* A HOL random engine *}

theory Random
imports Code_Numeral List
begin

notation fcomp (infixl "\<circ>>" 60)
notation scomp (infixl "\<circ>\<rightarrow>" 60)


subsection {* Auxiliary functions *}

fun log :: "code_numeral \<Rightarrow> code_numeral \<Rightarrow> code_numeral" where
  "log b i = (if b \<le> 1 \<or> i < b then 1 else 1 + log b (i div b))"

definition inc_shift :: "code_numeral \<Rightarrow> code_numeral \<Rightarrow> code_numeral" where
  "inc_shift v k = (if v = k then 1 else k + 1)"

definition minus_shift :: "code_numeral \<Rightarrow> code_numeral \<Rightarrow> code_numeral \<Rightarrow> code_numeral" where
  "minus_shift r k l = (if k < l then r + k - l else k - l)"


subsection {* Random seeds *}

type_synonym seed = "code_numeral \<times> code_numeral"

primrec "next" :: "seed \<Rightarrow> code_numeral \<times> seed" where
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


subsection {* Base selectors *}

fun iterate :: "code_numeral \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'b \<times> 'a) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<times> 'a" where
  "iterate k f x = (if k = 0 then Pair x else f x \<circ>\<rightarrow> iterate (k - 1) f)"

definition range :: "code_numeral \<Rightarrow> seed \<Rightarrow> code_numeral \<times> seed" where
  "range k = iterate (log 2147483561 k)
      (\<lambda>l. next \<circ>\<rightarrow> (\<lambda>v. Pair (v + l * 2147483561))) 1
    \<circ>\<rightarrow> (\<lambda>v. Pair (v mod k))"

lemma range:
  "k > 0 \<Longrightarrow> fst (range k s) < k"
  by (simp add: range_def split_def del: log.simps iterate.simps)

definition select :: "'a list \<Rightarrow> seed \<Rightarrow> 'a \<times> seed" where
  "select xs = range (Code_Numeral.of_nat (length xs))
    \<circ>\<rightarrow> (\<lambda>k. Pair (nth xs (Code_Numeral.nat_of k)))"
     
lemma select:
  assumes "xs \<noteq> []"
  shows "fst (select xs s) \<in> set xs"
proof -
  from assms have "Code_Numeral.of_nat (length xs) > 0" by simp
  with range have
    "fst (range (Code_Numeral.of_nat (length xs)) s) < Code_Numeral.of_nat (length xs)" by best
  then have
    "Code_Numeral.nat_of (fst (range (Code_Numeral.of_nat (length xs)) s)) < length xs" by simp
  then show ?thesis
    by (simp add: split_beta select_def)
qed

primrec pick :: "(code_numeral \<times> 'a) list \<Rightarrow> code_numeral \<Rightarrow> 'a" where
  "pick (x # xs) i = (if i < fst x then snd x else pick xs (i - fst x))"

lemma pick_member:
  "i < listsum (map fst xs) \<Longrightarrow> pick xs i \<in> set (map snd xs)"
  by (induct xs arbitrary: i) simp_all

lemma pick_drop_zero:
  "pick (filter (\<lambda>(k, _). k > 0) xs) = pick xs"
  by (induct xs) (auto simp add: fun_eq_iff)

lemma pick_same:
  "l < length xs \<Longrightarrow> Random.pick (map (Pair 1) xs) (Code_Numeral.of_nat l) = nth xs l"
proof (induct xs arbitrary: l)
  case Nil then show ?case by simp
next
  case (Cons x xs) then show ?case by (cases l) simp_all
qed

definition select_weight :: "(code_numeral \<times> 'a) list \<Rightarrow> seed \<Rightarrow> 'a \<times> seed" where
  "select_weight xs = range (listsum (map fst xs))
   \<circ>\<rightarrow> (\<lambda>k. Pair (pick xs k))"

lemma select_weight_member:
  assumes "0 < listsum (map fst xs)"
  shows "fst (select_weight xs s) \<in> set (map snd xs)"
proof -
  from range assms
    have "fst (range (listsum (map fst xs)) s) < listsum (map fst xs)" .
  with pick_member
    have "pick xs (fst (range (listsum (map fst xs)) s)) \<in> set (map snd xs)" .
  then show ?thesis by (simp add: select_weight_def scomp_def split_def) 
qed

lemma select_weight_cons_zero:
  "select_weight ((0, x) # xs) = select_weight xs"
  by (simp add: select_weight_def)

lemma select_weight_drop_zero:
  "select_weight (filter (\<lambda>(k, _). k > 0) xs) = select_weight xs"
proof -
  have "listsum (map fst [(k, _)\<leftarrow>xs . 0 < k]) = listsum (map fst xs)"
    by (induct xs) auto
  then show ?thesis by (simp only: select_weight_def pick_drop_zero)
qed

lemma select_weight_select:
  assumes "xs \<noteq> []"
  shows "select_weight (map (Pair 1) xs) = select xs"
proof -
  have less: "\<And>s. fst (range (Code_Numeral.of_nat (length xs)) s) < Code_Numeral.of_nat (length xs)"
    using assms by (intro range) simp
  moreover have "listsum (map fst (map (Pair 1) xs)) = Code_Numeral.of_nat (length xs)"
    by (induct xs) simp_all
  ultimately show ?thesis
    by (auto simp add: select_weight_def select_def scomp_def split_def
      fun_eq_iff pick_same [symmetric])
qed


subsection {* @{text ML} interface *}

code_reflect Random_Engine
  functions range select select_weight

ML {*
structure Random_Engine =
struct

open Random_Engine;

type seed = int * int;

local

val seed = Unsynchronized.ref 
  (let
    val now = Time.toMilliseconds (Time.now ());
    val (q, s1) = IntInf.divMod (now, 2147483562);
    val s2 = q mod 2147483398;
  in (s1 + 1, s2 + 1) end);

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
*}

hide_type (open) seed
hide_const (open) inc_shift minus_shift log "next" split_seed
  iterate range select pick select_weight
hide_fact (open) range_def

no_notation fcomp (infixl "\<circ>>" 60)
no_notation scomp (infixl "\<circ>\<rightarrow>" 60)

end
