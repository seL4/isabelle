(*  Title:      HOL/Library/Countable.thy
    Author:     Alexander Krauss, TU Muenchen
*)

header {* Encoding (almost) everything into natural numbers *}

theory Countable
imports Main Rat Nat_Bijection
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

instance prod :: (countable, countable) countable
  by (rule countable_classI [of "\<lambda>(x, y). prod_encode (to_nat x, to_nat y)"])
    (auto simp add: prod_encode_eq)


text {* Sums *}

instance sum :: (countable, countable) countable
  by (rule countable_classI [of "(\<lambda>x. case x of Inl a \<Rightarrow> to_nat (False, to_nat a)
                                     | Inr b \<Rightarrow> to_nat (True, to_nat b))"])
    (simp split: sum.split_asm)


text {* Integers *}

instance int :: countable
  by (rule countable_classI [of "int_encode"])
    (simp add: int_encode_eq)


text {* Options *}

instance option :: (countable) countable
  by (rule countable_classI [of "option_case 0 (Suc \<circ> to_nat)"])
    (simp split: option.split_asm)


text {* Lists *}

instance list :: (countable) countable
  by (rule countable_classI [of "list_encode \<circ> map to_nat"])
    (simp add: list_encode_eq)


text {* Further *}

instance String.literal :: countable
  by (rule countable_classI [of "String.literal_case to_nat"])
   (auto split: String.literal.splits)

instantiation typerep :: countable
begin

fun to_nat_typerep :: "typerep \<Rightarrow> nat" where
  "to_nat_typerep (Typerep.Typerep c ts) = to_nat (to_nat c, to_nat (map to_nat_typerep ts))"

instance proof (rule countable_classI)
  fix t t' :: typerep and ts ts' :: "typerep list"
  assume "to_nat_typerep t = to_nat_typerep t'"
  moreover have "to_nat_typerep t = to_nat_typerep t' \<Longrightarrow> t = t'"
    and "map to_nat_typerep ts = map to_nat_typerep ts' \<Longrightarrow> ts = ts'"
  proof (induct t and ts arbitrary: t' and ts' rule: typerep.inducts)
    case (Typerep c ts t')
    then obtain c' ts' where t': "t' = Typerep.Typerep c' ts'" by (cases t') auto
    with Typerep have "c = c'" and "ts = ts'" by simp_all
    with t' show "Typerep.Typerep c ts = t'" by simp
  next
    case Nil_typerep then show ?case by simp
  next
    case (Cons_typerep t ts) then show ?case by auto
  qed
  ultimately show "t = t'" by simp
qed

end


text {* Functions *}

instance "fun" :: (finite, countable) countable
proof
  obtain xs :: "'a list" where xs: "set xs = UNIV"
    using finite_list [OF finite_UNIV] ..
  show "\<exists>to_nat::('a \<Rightarrow> 'b) \<Rightarrow> nat. inj to_nat"
  proof
    show "inj (\<lambda>f. to_nat (map f xs))"
      by (rule injI, simp add: xs ext_iff)
  qed
qed


subsection {* The Rationals are Countably Infinite *}

definition nat_to_rat_surj :: "nat \<Rightarrow> rat" where
"nat_to_rat_surj n = (let (a,b) = prod_decode n
                      in Fract (int_decode a) (int_decode b))"

lemma surj_nat_to_rat_surj: "surj nat_to_rat_surj"
unfolding surj_def
proof
  fix r::rat
  show "\<exists>n. r = nat_to_rat_surj n"
  proof (cases r)
    fix i j assume [simp]: "r = Fract i j" and "j > 0"
    have "r = (let m = int_encode i; n = int_encode j
               in nat_to_rat_surj(prod_encode (m,n)))"
      by (simp add: Let_def nat_to_rat_surj_def)
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
