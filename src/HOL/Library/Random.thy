(* Author: Florian Haftmann, TU Muenchen *)

header {* A HOL random engine *}

theory Random
imports Code_Index
begin

notation fcomp (infixl "o>" 60)
notation scomp (infixl "o\<rightarrow>" 60)


subsection {* Auxiliary functions *}

definition inc_shift :: "index \<Rightarrow> index \<Rightarrow> index" where
  "inc_shift v k = (if v = k then 1 else k + 1)"

definition minus_shift :: "index \<Rightarrow> index \<Rightarrow> index \<Rightarrow> index" where
  "minus_shift r k l = (if k < l then r + k - l else k - l)"

fun log :: "index \<Rightarrow> index \<Rightarrow> index" where
  "log b i = (if b \<le> 1 \<or> i < b then 1 else 1 + log b (i div b))"


subsection {* Random seeds *}

types seed = "index \<times> index"

primrec "next" :: "seed \<Rightarrow> index \<times> seed" where
  "next (v, w) = (let
     k =  v div 53668;
     v' = minus_shift 2147483563 (40014 * (v mod 53668)) (k * 12211);
     l =  w div 52774;
     w' = minus_shift 2147483399 (40692 * (w mod 52774)) (l * 3791);
     z =  minus_shift 2147483562 v' (w' + 1) + 1
   in (z, (v', w')))"

lemma next_not_0:
  "fst (next s) \<noteq> 0"
  by (cases s) (auto simp add: minus_shift_def Let_def)

primrec seed_invariant :: "seed \<Rightarrow> bool" where
  "seed_invariant (v, w) \<longleftrightarrow> 0 < v \<and> v < 9438322952 \<and> 0 < w \<and> True"

lemma if_same: "(if b then f x else f y) = f (if b then x else y)"
  by (cases b) simp_all

definition split_seed :: "seed \<Rightarrow> seed \<times> seed" where
  "split_seed s = (let
     (v, w) = s;
     (v', w') = snd (next s);
     v'' = inc_shift 2147483562 v;
     s'' = (v'', w');
     w'' = inc_shift 2147483398 w;
     s''' = (v', w'')
   in (s'', s'''))"


subsection {* Base selectors *}

fun %quote iterate :: "index \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'b \<times> 'a) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<times> 'a" where
  "iterate k f x = (if k = 0 then Pair x else f x o\<rightarrow> iterate (k - 1) f)"

definition %quote range :: "index \<Rightarrow> seed \<Rightarrow> index \<times> seed" where
  "range k = iterate (log 2147483561 k)
      (\<lambda>l. next o\<rightarrow> (\<lambda>v. Pair (v + l * 2147483561))) 1
    o\<rightarrow> (\<lambda>v. Pair (v mod k))"

lemma range:
  "k > 0 \<Longrightarrow> fst (range k s) < k"
  by (simp add: range_def scomp_apply split_def del: log.simps iterate.simps)

definition select :: "'a list \<Rightarrow> seed \<Rightarrow> 'a \<times> seed" where
  "select xs = range (Code_Index.of_nat (length xs))
    o\<rightarrow> (\<lambda>k. Pair (nth xs (Code_Index.nat_of k)))"
     
lemma select:
  assumes "xs \<noteq> []"
  shows "fst (select xs s) \<in> set xs"
proof -
  from assms have "Code_Index.of_nat (length xs) > 0" by simp
  with range have
    "fst (range (Code_Index.of_nat (length xs)) s) < Code_Index.of_nat (length xs)" by best
  then have
    "Code_Index.nat_of (fst (range (Code_Index.of_nat (length xs)) s)) < length xs" by simp
  then show ?thesis
    by (simp add: scomp_apply split_beta select_def)
qed

definition select_default :: "index \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> seed \<Rightarrow> 'a \<times> seed" where
  [code del]: "select_default k x y = range k
     o\<rightarrow> (\<lambda>l. Pair (if l + 1 < k then x else y))"

lemma select_default_zero:
  "fst (select_default 0 x y s) = y"
  by (simp add: scomp_apply split_beta select_default_def)

lemma select_default_code [code]:
  "select_default k x y = (if k = 0
    then range 1 o\<rightarrow> (\<lambda>_. Pair y)
    else range k o\<rightarrow> (\<lambda>l. Pair (if l + 1 < k then x else y)))"
proof
  fix s
  have "snd (range (Code_Index.of_nat 0) s) = snd (range (Code_Index.of_nat 1) s)"
    by (simp add: range_def scomp_Pair scomp_apply split_beta)
  then show "select_default k x y s = (if k = 0
    then range 1 o\<rightarrow> (\<lambda>_. Pair y)
    else range k o\<rightarrow> (\<lambda>l. Pair (if l + 1 < k then x else y))) s"
    by (cases "k = 0") (simp_all add: select_default_def scomp_apply split_beta)
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

no_notation fcomp (infixl "o>" 60)
no_notation scomp (infixl "o\<rightarrow>" 60)

end

