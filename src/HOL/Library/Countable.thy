(*  Title:      HOL/Library/Countable.thy
    Author:     Alexander Krauss, TU Muenchen
*)

header {* Encoding (almost) everything into natural numbers *}

theory Countable
imports
  "~~/src/HOL/List"
  "~~/src/HOL/Hilbert_Choice"
  "~~/src/HOL/Nat_Int_Bij"
  "~~/src/HOL/Rational"
  Main
begin

subsection {* The class of countable types *}

class countable =
  assumes ex_inj: "\<exists>to_nat \<Colon> 'a \<Rightarrow> nat. inj to_nat"

lemma countable_classI:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "\<And>x y. f x = f y \<Longrightarrow> x = y"
  shows "OFCLASS('a, countable_class)"
proof (intro_classes, rule exI)
  show "inj f"
    by (rule injI [OF assms]) assumption
qed


subsection {* Conversion functions *}

definition to_nat :: "'a\<Colon>countable \<Rightarrow> nat" where
  "to_nat = (SOME f. inj f)"

definition from_nat :: "nat \<Rightarrow> 'a\<Colon>countable" where
  "from_nat = inv (to_nat \<Colon> 'a \<Rightarrow> nat)"

lemma inj_to_nat [simp]: "inj to_nat"
  by (rule exE_some [OF ex_inj]) (simp add: to_nat_def)

lemma surj_from_nat [simp]: "surj from_nat"
  unfolding from_nat_def by (simp add: inj_imp_surj_inv)

lemma to_nat_split [simp]: "to_nat x = to_nat y \<longleftrightarrow> x = y"
  using injD [OF inj_to_nat] by auto

lemma from_nat_to_nat [simp]:
  "from_nat (to_nat x) = x"
  by (simp add: from_nat_def)


subsection {* Countable types *}

instance nat :: countable
  by (rule countable_classI [of "id"]) simp 

subclass (in finite) countable
proof
  have "finite (UNIV\<Colon>'a set)" by (rule finite_UNIV)
  with finite_conv_nat_seg_image [of "UNIV::'a set"]
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
apply atomize_elim
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


text {* Functions *}

instance "fun" :: (finite, countable) countable
proof
  obtain xs :: "'a list" where xs: "set xs = UNIV"
    using finite_list [OF finite_UNIV] ..
  show "\<exists>to_nat::('a \<Rightarrow> 'b) \<Rightarrow> nat. inj to_nat"
  proof
    show "inj (\<lambda>f. to_nat (map f xs))"
      by (rule injI, simp add: xs expand_fun_eq)
  qed
qed


subsection {* The Rationals are Countably Infinite *}

definition nat_to_rat_surj :: "nat \<Rightarrow> rat" where
"nat_to_rat_surj n = (let (a,b) = nat_to_nat2 n
                      in Fract (nat_to_int_bij a) (nat_to_int_bij b))"

lemma surj_nat_to_rat_surj: "surj nat_to_rat_surj"
unfolding surj_def
proof
  fix r::rat
  show "\<exists>n. r = nat_to_rat_surj n"
  proof(cases r)
    fix i j assume [simp]: "r = Fract i j" and "j \<noteq> 0"
    have "r = (let m = inv nat_to_int_bij i; n = inv nat_to_int_bij j
               in nat_to_rat_surj(nat2_to_nat (m,n)))"
      using nat2_to_nat_inj surj_f_inv_f[OF surj_nat_to_int_bij]
      by(simp add:Let_def nat_to_rat_surj_def nat_to_nat2_def)
    thus "\<exists>n. r = nat_to_rat_surj n" by(auto simp:Let_def)
  qed
qed

lemma Rats_eq_range_nat_to_rat_surj: "\<rat> = range nat_to_rat_surj"
by (simp add: Rats_def surj_nat_to_rat_surj surj_range)

context field_char_0
begin

lemma Rats_eq_range_of_rat_o_nat_to_rat_surj:
  "\<rat> = range (of_rat o nat_to_rat_surj)"
using surj_nat_to_rat_surj
by (auto simp: Rats_def image_def surj_def)
   (blast intro: arg_cong[where f = of_rat])

lemma surj_of_rat_nat_to_rat_surj:
  "r\<in>\<rat> \<Longrightarrow> \<exists>n. r = of_rat(nat_to_rat_surj n)"
by(simp add: Rats_eq_range_of_rat_o_nat_to_rat_surj image_def)

end

instance rat :: countable
proof
  show "\<exists>to_nat::rat \<Rightarrow> nat. inj to_nat"
  proof
    have "surj nat_to_rat_surj"
      by (rule surj_nat_to_rat_surj)
    then show "inj (inv nat_to_rat_surj)"
      by (rule surj_imp_inj_inv)
  qed
qed

end
