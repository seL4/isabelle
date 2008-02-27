(*  Title:      HOL/Library/Countable.thy
    ID:         $Id$
    Author:     Tobias Nipkow
*)

header {* Encoding (almost) everything into natural numbers *}

theory Countable
imports Finite_Set List Hilbert_Choice
begin

subsection {* The class of countable types *}

class countable = itself +
  assumes ex_inj: "\<exists>to_nat \<Colon> 'a \<Rightarrow> nat. inj to_nat"

lemma countable_classI:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "\<And>x y. f x = f y \<Longrightarrow> x = y"
  shows "OFCLASS('a, countable_class)"
proof (intro_classes, rule exI)
  show "inj f"
    by (rule injI [OF assms]) assumption
qed


subsection {* Converion functions *}

definition to_nat :: "'a\<Colon>countable \<Rightarrow> nat" where
  "to_nat = (SOME f. inj f)"

definition from_nat :: "nat \<Rightarrow> 'a\<Colon>countable" where
  "from_nat = inv (to_nat \<Colon> 'a \<Rightarrow> nat)"

lemma inj_to_nat [simp]: "inj to_nat"
  by (rule exE_some [OF ex_inj]) (simp add: to_nat_def)

lemma to_nat_split [simp]: "to_nat x = to_nat y \<longleftrightarrow> x = y"
  using injD [OF inj_to_nat] by auto

lemma from_nat_to_nat [simp]:
  "from_nat (to_nat x) = x"
  by (simp add: from_nat_def)


subsection {* Countable types *}

instance nat :: countable
  by (rule countable_classI [of "id"]) simp 

subclass (in finite) countable
proof unfold_locales
  have "finite (UNIV\<Colon>'a set)" by (rule finite_UNIV)
  with finite_conv_nat_seg_image [of UNIV]
  obtain n and f :: "nat \<Rightarrow> 'a" 
    where "UNIV = f ` {i. i < n}" by auto
  then have "surj f" unfolding surj_def by auto
  then have "inj (inv f)" by (rule surj_imp_inj_inv)
  then show "\<exists>to_nat \<Colon> 'a \<Rightarrow> nat. inj to_nat" by (rule exI[of inj])
qed

text {* Pairs *}

primrec sum :: "nat \<Rightarrow> nat"
where
  "sum 0 = 0"
| "sum (Suc n) = Suc n + sum n"

lemma sum_arith: "sum n = n * Suc n div 2"
  by (induct n) auto

lemma sum_mono: "n \<ge> m \<Longrightarrow> sum n \<ge> sum m"
  by (induct n m rule: diff_induct) auto

definition
  "pair_encode = (\<lambda>(m, n). sum (m + n) + m)"

lemma inj_pair_cencode: "inj pair_encode"
  unfolding pair_encode_def
proof (rule injI, simp only: split_paired_all split_conv)
  fix a b c d
  assume eq: "sum (a + b) + a = sum (c + d) + c"
  have "a + b = c + d \<or> a + b \<ge> Suc (c + d) \<or> c + d \<ge> Suc (a + b)" by arith
  then
  show "(a, b) = (c, d)"
  proof (elim disjE)
    assume sumeq: "a + b = c + d"
    then have "a = c" using eq by auto
    moreover from sumeq this have "b = d" by auto
    ultimately show ?thesis by simp
  next
    assume "a + b \<ge> Suc (c + d)"
    from sum_mono[OF this] eq
    show ?thesis by auto
  next
    assume "c + d \<ge> Suc (a + b)"
    from sum_mono[OF this] eq
    show ?thesis by auto
  qed
qed

instance "*" :: (countable, countable) countable
by (rule countable_classI [of "\<lambda>(x, y). pair_encode (to_nat x, to_nat y)"])
  (auto dest: injD [OF inj_pair_cencode] injD [OF inj_to_nat])


text {* Sums *}

instance "+":: (countable, countable) countable
  by (rule countable_classI [of "(\<lambda>x. case x of Inl a \<Rightarrow> to_nat (False, to_nat a)
                                     | Inr b \<Rightarrow> to_nat (True, to_nat b))"])
    (auto split:sum.splits)


text {* Integers *}

lemma int_cases: "(i::int) = 0 \<or> i < 0 \<or> i > 0"
by presburger

lemma int_pos_neg_zero:
  obtains (zero) "(z::int) = 0" "sgn z = 0" "abs z = 0"
  | (pos) n where "z = of_nat n" "sgn z = 1" "abs z = of_nat n"
  | (neg) n where "z = - (of_nat n)" "sgn z = -1" "abs z = of_nat n"
apply elim_to_cases
apply (insert int_cases[of z])
apply (auto simp:zsgn_def)
apply (rule_tac x="nat (-z)" in exI, simp)
apply (rule_tac x="nat z" in exI, simp)
done

instance int :: countable
proof (rule countable_classI [of "(\<lambda>i. to_nat (nat (sgn i + 1), nat (abs i)))"], 
    auto dest: injD [OF inj_to_nat])
  fix x y 
  assume a: "nat (sgn x + 1) = nat (sgn y + 1)" "nat (abs x) = nat (abs y)"
  show "x = y"
  proof (cases rule: int_pos_neg_zero[of x])
    case zero 
    with a show "x = y" by (cases rule: int_pos_neg_zero[of y]) auto
  next
    case (pos n)
    with a show "x = y" by (cases rule: int_pos_neg_zero[of y]) auto
  next
    case (neg n)
    with a show "x = y" by (cases rule: int_pos_neg_zero[of y]) auto
  qed
qed


text {* Options *}

instance option :: (countable) countable
by (rule countable_classI[of "\<lambda>x. case x of None \<Rightarrow> 0
                                     | Some y \<Rightarrow> Suc (to_nat y)"])
 (auto split:option.splits)


text {* Lists *}

lemma from_nat_to_nat_map [simp]: "map from_nat (map to_nat xs) = xs"
  by (simp add: comp_def map_compose [symmetric])

primrec
  list_encode :: "'a\<Colon>countable list \<Rightarrow> nat"
where
  "list_encode [] = 0"
| "list_encode (x#xs) = Suc (to_nat (x, list_encode xs))"

instance list :: (countable) countable
proof (rule countable_classI [of "list_encode"])
  fix xs ys :: "'a list"
  assume cenc: "list_encode xs = list_encode ys"
  then show "xs = ys"
  proof (induct xs arbitrary: ys)
    case (Nil ys)
    with cenc show ?case by (cases ys, auto)
  next
    case (Cons x xs' ys)
    thus ?case by (cases ys) auto
  qed
qed

end
