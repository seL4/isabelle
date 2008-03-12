(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* A HOL random engine *}

theory Random
imports State_Monad Code_Index
begin

subsection {* Auxiliary functions *}

definition
  inc_shift :: "index \<Rightarrow> index \<Rightarrow> index"
where
  "inc_shift v k = (if v = k then 1 else k + 1)"

definition
  minus_shift :: "index \<Rightarrow> index \<Rightarrow> index \<Rightarrow> index"
where
  "minus_shift r k l = (if k < l then r + k - l else k - l)"

function
  log :: "index \<Rightarrow> index \<Rightarrow> index"
where
  "log b i = (if b \<le> 1 \<or> i < b then 1 else 1 + log b (i div b))"
by pat_completeness auto
termination
  by (relation "measure (nat_of_index o snd)")
    (auto simp add: index)


subsection {* Random seeds *}

types seed = "index \<times> index"

primrec
  "next" :: "seed \<Rightarrow> index \<times> seed"
where
  "next (v, w) = (let
     k =  v div 53668;
     v' = minus_shift 2147483563 (40014 * (v mod 53668)) (k * 12211);
     l =  w div 52774;
     w' = minus_shift 2147483399 (40692 * (w mod 52774)) (l * 3791);
     z =  minus_shift 2147483562 v' (w' + 1) + 1
   in (z, (v', w')))"

lemma next_not_0:
  "fst (next s) \<noteq> 0"
apply (cases s)
apply (auto simp add: minus_shift_def Let_def)
done

primrec
  seed_invariant :: "seed \<Rightarrow> bool"
where
  "seed_invariant (v, w) \<longleftrightarrow> 0 < v \<and> v < 9438322952 \<and> 0 < w \<and> True"

lemma if_same:
  "(if b then f x else f y) = f (if b then x else y)"
  by (cases b) simp_all

(*lemma seed_invariant:
  assumes "seed_invariant (index_of_nat v, index_of_nat w)"
    and "(index_of_nat z, (index_of_nat v', index_of_nat w')) = next (index_of_nat v, index_of_nat w)"
  shows "seed_invariant (index_of_nat v', index_of_nat w')"
using assms
apply (auto simp add: seed_invariant_def)
apply (auto simp add: minus_shift_def Let_def)
apply (simp_all add: if_same cong del: if_cong)
apply safe
unfolding not_less
oops*)

definition
  split_seed :: "seed \<Rightarrow> seed \<times> seed"
where
  "split_seed s = (let
     (v, w) = s;
     (v', w') = snd (next s);
     v'' = inc_shift 2147483562 v;
     s'' = (v'', w');
     w'' = inc_shift 2147483398 w;
     s''' = (v', w'')
   in (s'', s'''))"


subsection {* Base selectors *}

function
  range_aux :: "index \<Rightarrow> index \<Rightarrow> seed \<Rightarrow> index \<times> seed"
where
  "range_aux k l s = (if k = 0 then (l, s) else
    let (v, s') = next s
  in range_aux (k - 1) (v + l * 2147483561) s')"
by pat_completeness auto
termination
  by (relation "measure (nat_of_index o fst)")
    (auto simp add: index)

definition
  range :: "index \<Rightarrow> seed \<Rightarrow> index \<times> seed"
where
  "range k = (do
     v \<leftarrow> range_aux (log 2147483561 k) 1;
     return (v mod k)
   done)"

lemma range:
  assumes "k > 0"
  shows "fst (range k s) < k"
proof -
  obtain v w where range_aux:
    "range_aux (log 2147483561 k) 1 s = (v, w)"
    by (cases "range_aux (log 2147483561 k) 1 s")
  with assms show ?thesis
    by (simp add: range_def run_def mbind_def split_def del: range_aux.simps log.simps)
qed

definition
  select :: "'a list \<Rightarrow> seed \<Rightarrow> 'a \<times> seed"
where
  "select xs = (do
     k \<leftarrow> range (index_of_nat (length xs));
     return (nth xs (nat_of_index k))
   done)"

lemma select:
  assumes "xs \<noteq> []"
  shows "fst (select xs s) \<in> set xs"
proof -
  from assms have "index_of_nat (length xs) > 0" by simp
  with range have
    "fst (range (index_of_nat (length xs)) s) < index_of_nat (length xs)" by best
  then have
    "nat_of_index (fst (range (index_of_nat (length xs)) s)) < length xs" by simp
  then show ?thesis
    by (auto simp add: select_def run_def mbind_def split_def)
qed

definition
  select_default :: "index \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> seed \<Rightarrow> 'a \<times> seed"
where
  [code func del]: "select_default k x y = (do
     l \<leftarrow> range k;
     return (if l + 1 < k then x else y)
   done)"

lemma select_default_zero:
  "fst (select_default 0 x y s) = y"
  by (simp add: run_def mbind_def split_def select_default_def)

lemma select_default_code [code]:
  "select_default k x y = (if k = 0 then do
     _ \<leftarrow> range 1;
     return y
   done else do
     l \<leftarrow> range k;
     return (if l + 1 < k then x else y)
   done)"
proof (cases "k = 0")
  case False then show ?thesis by (simp add: select_default_def)
next
  case True then show ?thesis
    by (simp add: run_def mbind_def split_def select_default_def expand_fun_eq range_def)
qed


subsection {* @{text ML} interface *}

ML {*
structure Random_Engine =
struct

type seed = int * int;

local

val seed = ref 
  (let
    val now = Time.toMilliseconds (Time.now ());
    val (q, s1) = IntInf.divMod (now, 2147483562);
    val s2 = q mod 2147483398;
  in (s1 + 1, s2 + 1) end);

in

fun run f =
  let
    val (x, seed') = f (! seed);
    val _ = seed := seed'
  in x end;

end;

end;
*}

end
