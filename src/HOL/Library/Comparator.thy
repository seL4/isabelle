(*  Title:      HOL/Library/Comparator.thy
    Author:     Florian Haftmann, TU Muenchen
*)

theory Comparator
  imports Main
begin

section \<open>Comparators on linear quasi-orders\<close>

datatype comp = Less | Equiv | Greater

locale comparator =
  fixes cmp :: "'a \<Rightarrow> 'a \<Rightarrow> comp"
  assumes refl [simp]: "\<And>a. cmp a a = Equiv"
    and trans_equiv: "\<And>a b c. cmp a b = Equiv \<Longrightarrow> cmp b c = Equiv \<Longrightarrow> cmp a c = Equiv"
  assumes trans_less: "cmp a b = Less \<Longrightarrow> cmp b c = Less \<Longrightarrow> cmp a c = Less"
    and greater_iff_sym_less: "\<And>b a. cmp b a = Greater \<longleftrightarrow> cmp a b = Less"
begin

text \<open>Dual properties\<close>

lemma trans_greater:
  "cmp a c = Greater" if "cmp a b = Greater" "cmp b c = Greater"
  using that greater_iff_sym_less trans_less by blast

lemma less_iff_sym_greater:
  "cmp b a = Less \<longleftrightarrow> cmp a b = Greater"
  by (simp add: greater_iff_sym_less)

text \<open>The equivalence part\<close>

lemma sym:
  "cmp b a = Equiv \<longleftrightarrow> cmp a b = Equiv"
  by (metis (full_types) comp.exhaust greater_iff_sym_less)

lemma reflp:
  "reflp (\<lambda>a b. cmp a b = Equiv)"
  by (rule reflpI) simp

lemma symp:
  "symp (\<lambda>a b. cmp a b = Equiv)"
  by (rule sympI) (simp add: sym)

lemma transp:
  "transp (\<lambda>a b. cmp a b = Equiv)"
  by (rule transpI) (fact trans_equiv)

lemma equivp:
  "equivp (\<lambda>a b. cmp a b = Equiv)"
  using reflp symp transp by (rule equivpI)

text \<open>The strict part\<close>

lemma irreflp_less:
  "irreflp (\<lambda>a b. cmp a b = Less)"
  by (rule irreflpI) simp

lemma irreflp_greater:
  "irreflp (\<lambda>a b. cmp a b = Greater)"
  by (rule irreflpI) simp

lemma asym_less:
  "cmp b a \<noteq> Less" if "cmp a b = Less"
  using that greater_iff_sym_less by force

lemma asym_greater:
  "cmp b a \<noteq> Greater" if "cmp a b = Greater"
  using that greater_iff_sym_less by force

lemma asymp_less:
  "asymp (\<lambda>a b. cmp a b = Less)"
  using irreflp_less by (auto intro: asympI dest: asym_less)

lemma asymp_greater:
  "asymp (\<lambda>a b. cmp a b = Greater)"
  using irreflp_greater by (auto intro!: asympI dest: asym_greater)

lemma trans_equiv_less:
  "cmp a c = Less" if "cmp a b = Equiv" and "cmp b c = Less"
  using that
  by (metis (full_types) comp.exhaust greater_iff_sym_less trans_equiv trans_less)

lemma trans_less_equiv:
  "cmp a c = Less" if "cmp a b = Less" and "cmp b c = Equiv"
  using that
  by (metis (full_types) comp.exhaust greater_iff_sym_less trans_equiv trans_less)

lemma trans_equiv_greater:
  "cmp a c = Greater" if "cmp a b = Equiv" and "cmp b c = Greater"
  using that by (simp add: sym [of a b] greater_iff_sym_less trans_less_equiv)

lemma trans_greater_equiv:
  "cmp a c = Greater" if "cmp a b = Greater" and "cmp b c = Equiv"
  using that by (simp add: sym [of b c] greater_iff_sym_less trans_equiv_less)

lemma transp_less:
  "transp (\<lambda>a b. cmp a b = Less)"
  by (rule transpI) (fact trans_less)

lemma transp_greater:
  "transp (\<lambda>a b. cmp a b = Greater)"
  by (rule transpI) (fact trans_greater)

text \<open>The reflexive part\<close>

lemma reflp_not_less:
  "reflp (\<lambda>a b. cmp a b \<noteq> Less)"
  by (rule reflpI) simp

lemma reflp_not_greater:
  "reflp (\<lambda>a b. cmp a b \<noteq> Greater)"
  by (rule reflpI) simp

lemma quasisym_not_less:
  "cmp a b = Equiv" if "cmp a b \<noteq> Less" and "cmp b a \<noteq> Less"
  using that comp.exhaust greater_iff_sym_less by auto

lemma quasisym_not_greater:
  "cmp a b = Equiv" if "cmp a b \<noteq> Greater" and "cmp b a \<noteq> Greater"
  using that comp.exhaust greater_iff_sym_less by auto

lemma trans_not_less:
  "cmp a c \<noteq> Less" if "cmp a b \<noteq> Less" "cmp b c \<noteq> Less"
  using that by (metis comp.exhaust greater_iff_sym_less trans_equiv trans_less)

lemma trans_not_greater:
  "cmp a c \<noteq> Greater" if "cmp a b \<noteq> Greater" "cmp b c \<noteq> Greater"
  using that greater_iff_sym_less trans_not_less by blast

lemma transp_not_less:
  "transp (\<lambda>a b. cmp a b \<noteq> Less)"
  by (rule transpI) (fact trans_not_less)

lemma transp_not_greater:
  "transp (\<lambda>a b. cmp a b \<noteq> Greater)"
  by (rule transpI) (fact trans_not_greater)

text \<open>Substitution under equivalences\<close>

lemma equiv_subst_left:
  "cmp z y = comp \<longleftrightarrow> cmp x y = comp" if "cmp z x = Equiv" for comp
proof -
  from that have "cmp x z = Equiv"
    by (simp add: sym)
  with that show ?thesis
    by (cases comp) (auto intro: trans_equiv trans_equiv_less trans_equiv_greater)
qed

lemma equiv_subst_right:
  "cmp x z = comp \<longleftrightarrow> cmp x y = comp" if "cmp z y = Equiv" for comp
proof -
  from that have "cmp y z = Equiv"
    by (simp add: sym)
  with that show ?thesis
    by (cases comp) (auto intro: trans_equiv trans_less_equiv trans_greater_equiv)
qed

end

typedef 'a comparator = "{cmp :: 'a \<Rightarrow> 'a \<Rightarrow> comp. comparator cmp}"
  morphisms compare Abs_comparator
proof -
  have "comparator (\<lambda>_ _. Equiv)"
    by standard simp_all
  then show ?thesis
    by auto
qed

setup_lifting type_definition_comparator

global_interpretation compare: comparator "compare cmp"
  using compare [of cmp] by simp

lift_definition flat :: "'a comparator"
  is "\<lambda>_ _. Equiv" by standard simp_all

instantiation comparator :: (linorder) default
begin

lift_definition default_comparator :: "'a comparator"
  is "\<lambda>x y. if x < y then Less else if x > y then Greater else Equiv"
  by standard (auto split: if_splits)

instance ..

end

text \<open>A rudimentary quickcheck setup\<close>

instantiation comparator :: (enum) equal
begin

lift_definition equal_comparator :: "'a comparator \<Rightarrow> 'a comparator \<Rightarrow> bool"
  is "\<lambda>f g. \<forall>x \<in> set Enum.enum. f x = g x" .

instance
  by (standard; transfer) (auto simp add: enum_UNIV)

end

lemma [code]:
  "HOL.equal cmp1 cmp2 \<longleftrightarrow> Enum.enum_all (\<lambda>x. compare cmp1 x = compare cmp2 x)"
  by transfer (simp add: enum_UNIV)

lemma [code nbe]:
  "HOL.equal (cmp :: 'a::enum comparator) cmp \<longleftrightarrow> True"
  by (fact equal_refl)

instantiation comparator :: ("{linorder, typerep}") full_exhaustive
begin

definition full_exhaustive_comparator ::
  "('a comparator \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option)
    \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"
  where "full_exhaustive_comparator f s =
    Quickcheck_Exhaustive.orelse
      (f (flat, (\<lambda>u. Code_Evaluation.Const (STR ''Comparator.flat'') TYPEREP('a comparator))))
      (f (default, (\<lambda>u. Code_Evaluation.Const (STR ''HOL.default_class.default'') TYPEREP('a comparator))))"

instance ..

end

text \<open>Fundamental comparator combinators\<close>

lift_definition reversed :: "'a comparator \<Rightarrow> 'a comparator"
  is "\<lambda>cmp a b. cmp b a"
proof -
  fix cmp :: "'a \<Rightarrow> 'a \<Rightarrow> comp"
  assume "comparator cmp"
  then interpret comparator cmp .
  show "comparator (\<lambda>a b. cmp b a)"
    by standard (auto intro: trans_equiv trans_less simp: greater_iff_sym_less)
qed

lift_definition key :: "('b \<Rightarrow> 'a) \<Rightarrow> 'a comparator \<Rightarrow> 'b comparator"
  is "\<lambda>f cmp a b. cmp (f a) (f b)"
proof -
  fix cmp :: "'a \<Rightarrow> 'a \<Rightarrow> comp" and f :: "'b \<Rightarrow> 'a"
  assume "comparator cmp"
  then interpret comparator cmp .
  show "comparator (\<lambda>a b. cmp (f a) (f b))"
    by standard (auto intro: trans_equiv trans_less simp: greater_iff_sym_less)
qed

end
