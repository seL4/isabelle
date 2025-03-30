(*  Title:      HOL/Library/Comparator.thy
    Author:     Florian Haftmann, TU Muenchen
*)

theory Comparator
  imports Main
begin

section \<open>Comparators on linear quasi-orders\<close>

subsection \<open>Basic properties\<close>

datatype comp = Less | Equiv | Greater

locale comparator =
  fixes cmp :: \<open>'a \<Rightarrow> 'a \<Rightarrow> comp\<close>
  assumes refl [simp]: \<open>\<And>a. cmp a a = Equiv\<close>
    and trans_equiv: \<open>\<And>a b c. cmp a b = Equiv \<Longrightarrow> cmp b c = Equiv \<Longrightarrow> cmp a c = Equiv\<close>
  assumes trans_less: \<open>cmp a b = Less \<Longrightarrow> cmp b c = Less \<Longrightarrow> cmp a c = Less\<close>
    and greater_iff_sym_less: \<open>\<And>b a. cmp b a = Greater \<longleftrightarrow> cmp a b = Less\<close>
begin

text \<open>Dual properties\<close>

lemma trans_greater:
  \<open>cmp a c = Greater\<close> if \<open>cmp a b = Greater\<close> \<open>cmp b c = Greater\<close>
  using that greater_iff_sym_less trans_less by blast

lemma less_iff_sym_greater:
  \<open>cmp b a = Less \<longleftrightarrow> cmp a b = Greater\<close>
  by (simp add: greater_iff_sym_less)

text \<open>The equivalence part\<close>

lemma sym:
  \<open>cmp b a = Equiv \<longleftrightarrow> cmp a b = Equiv\<close>
  by (metis (full_types) comp.exhaust greater_iff_sym_less)

lemma reflp:
  \<open>reflp (\<lambda>a b. cmp a b = Equiv)\<close>
  by (rule reflpI) simp

lemma symp:
  \<open>symp (\<lambda>a b. cmp a b = Equiv)\<close>
  by (rule sympI) (simp add: sym)

lemma transp:
  \<open>transp (\<lambda>a b. cmp a b = Equiv)\<close>
  by (rule transpI) (fact trans_equiv)

lemma equivp:
  \<open>equivp (\<lambda>a b. cmp a b = Equiv)\<close>
  using reflp symp transp by (rule equivpI)

text \<open>The strict part\<close>

lemma irreflp_less:
  \<open>irreflp (\<lambda>a b. cmp a b = Less)\<close>
  by (rule irreflpI) simp

lemma irreflp_greater:
  \<open>irreflp (\<lambda>a b. cmp a b = Greater)\<close>
  by (rule irreflpI) simp

lemma asym_less:
  \<open>cmp b a \<noteq> Less\<close> if \<open>cmp a b = Less\<close>
  using that greater_iff_sym_less by force

lemma asym_greater:
  \<open>cmp b a \<noteq> Greater\<close> if \<open>cmp a b = Greater\<close>
  using that greater_iff_sym_less by force

lemma asymp_less:
  \<open>asymp (\<lambda>a b. cmp a b = Less)\<close>
  using irreflp_less by (auto dest: asym_less)

lemma asymp_greater:
  \<open>asymp (\<lambda>a b. cmp a b = Greater)\<close>
  using irreflp_greater by (auto dest: asym_greater)

lemma trans_equiv_less:
  \<open>cmp a c = Less\<close> if \<open>cmp a b = Equiv\<close> and \<open>cmp b c = Less\<close>
  using that
  by (metis (full_types) comp.exhaust greater_iff_sym_less trans_equiv trans_less)

lemma trans_less_equiv:
  \<open>cmp a c = Less\<close> if \<open>cmp a b = Less\<close> and \<open>cmp b c = Equiv\<close>
  using that
  by (metis (full_types) comp.exhaust greater_iff_sym_less trans_equiv trans_less)

lemma trans_equiv_greater:
  \<open>cmp a c = Greater\<close> if \<open>cmp a b = Equiv\<close> and \<open>cmp b c = Greater\<close>
  using that by (simp add: sym [of a b] greater_iff_sym_less trans_less_equiv)

lemma trans_greater_equiv:
  \<open>cmp a c = Greater\<close> if \<open>cmp a b = Greater\<close> and \<open>cmp b c = Equiv\<close>
  using that by (simp add: sym [of b c] greater_iff_sym_less trans_equiv_less)

lemma transp_less:
  \<open>transp (\<lambda>a b. cmp a b = Less)\<close>
  by (rule transpI) (fact trans_less)

lemma transp_greater:
  \<open>transp (\<lambda>a b. cmp a b = Greater)\<close>
  by (rule transpI) (fact trans_greater)

text \<open>The reflexive part\<close>

lemma reflp_not_less:
  \<open>reflp (\<lambda>a b. cmp a b \<noteq> Less)\<close>
  by (rule reflpI) simp

lemma reflp_not_greater:
  \<open>reflp (\<lambda>a b. cmp a b \<noteq> Greater)\<close>
  by (rule reflpI) simp

lemma quasisym_not_less:
  \<open>cmp a b = Equiv\<close> if \<open>cmp a b \<noteq> Less\<close> and \<open>cmp b a \<noteq> Less\<close>
  using that comp.exhaust greater_iff_sym_less by auto

lemma quasisym_not_greater:
  \<open>cmp a b = Equiv\<close> if \<open>cmp a b \<noteq> Greater\<close> and \<open>cmp b a \<noteq> Greater\<close>
  using that comp.exhaust greater_iff_sym_less by auto

lemma trans_not_less:
  \<open>cmp a c \<noteq> Less\<close> if \<open>cmp a b \<noteq> Less\<close> \<open>cmp b c \<noteq> Less\<close>
  using that by (metis comp.exhaust greater_iff_sym_less trans_equiv trans_less)

lemma trans_not_greater:
  \<open>cmp a c \<noteq> Greater\<close> if \<open>cmp a b \<noteq> Greater\<close> \<open>cmp b c \<noteq> Greater\<close>
  using that greater_iff_sym_less trans_not_less by blast

lemma transp_not_less:
  \<open>transp (\<lambda>a b. cmp a b \<noteq> Less)\<close>
  by (rule transpI) (fact trans_not_less)

lemma transp_not_greater:
  \<open>transp (\<lambda>a b. cmp a b \<noteq> Greater)\<close>
  by (rule transpI) (fact trans_not_greater)

text \<open>Substitution under equivalences\<close>

lemma equiv_subst_left:
  \<open>cmp z y = comp \<longleftrightarrow> cmp x y = comp\<close> if \<open>cmp z x = Equiv\<close> for comp
proof -
  from that have \<open>cmp x z = Equiv\<close>
    by (simp add: sym)
  with that show ?thesis
    by (cases comp) (auto intro: trans_equiv trans_equiv_less trans_equiv_greater)
qed

lemma equiv_subst_right:
  \<open>cmp x z = comp \<longleftrightarrow> cmp x y = comp\<close> if \<open>cmp z y = Equiv\<close> for comp
proof -
  from that have \<open>cmp y z = Equiv\<close>
    by (simp add: sym)
  with that show ?thesis
    by (cases comp) (auto intro: trans_equiv trans_less_equiv trans_greater_equiv)
qed

end

typedef 'a comparator = \<open>{cmp :: 'a \<Rightarrow> 'a \<Rightarrow> comp. comparator cmp}\<close>
  morphisms compare Abs_comparator
proof -
  have \<open>comparator (\<lambda>_ _. Equiv)\<close>
    by standard simp_all
  then show ?thesis
    by auto
qed

setup_lifting type_definition_comparator

global_interpretation compare: comparator \<open>compare cmp\<close>
  using compare [of cmp] by simp

lift_definition flat :: \<open>'a comparator\<close>
  is \<open>\<lambda>_ _. Equiv\<close> by standard simp_all

instantiation comparator :: (linorder) default
begin

lift_definition default_comparator :: \<open>'a comparator\<close>
  is \<open>\<lambda>x y. if x < y then Less else if x > y then Greater else Equiv\<close>
  by standard (auto split: if_splits)

instance ..

end

text \<open>A rudimentary quickcheck setup\<close>

instantiation comparator :: (enum) equal
begin

lift_definition equal_comparator :: \<open>'a comparator \<Rightarrow> 'a comparator \<Rightarrow> bool\<close>
  is \<open>\<lambda>f g. \<forall>x \<in> set Enum.enum. f x = g x\<close> .

instance
  by (standard; transfer) (auto simp add: enum_UNIV)

end

lemma [code]:
  \<open>HOL.equal cmp1 cmp2 \<longleftrightarrow> Enum.enum_all (\<lambda>x. compare cmp1 x = compare cmp2 x)\<close>
  by transfer (simp add: enum_UNIV)

lemma [code nbe]:
  \<open>HOL.equal (cmp :: 'a::enum comparator) cmp \<longleftrightarrow> True\<close>
  by (fact equal_refl)

instantiation comparator :: ("{linorder, typerep}") full_exhaustive
begin

definition full_exhaustive_comparator ::
  \<open>('a comparator \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option)
    \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option\<close>
  where \<open>full_exhaustive_comparator f s =
    Quickcheck_Exhaustive.orelse
      (f (flat, (\<lambda>u. Code_Evaluation.Const (STR ''Comparator.flat'') TYPEREP('a comparator))))
      (f (default, (\<lambda>u. Code_Evaluation.Const (STR ''HOL.default_class.default'') TYPEREP('a comparator))))\<close>

instance ..

end


subsection \<open>Fundamental comparator combinators\<close>

lift_definition reversed :: \<open>'a comparator \<Rightarrow> 'a comparator\<close>
  is \<open>\<lambda>cmp a b. cmp b a\<close>
proof -
  fix cmp :: \<open>'a \<Rightarrow> 'a \<Rightarrow> comp\<close>
  assume \<open>comparator cmp\<close>
  then interpret comparator cmp .
  show \<open>comparator (\<lambda>a b. cmp b a)\<close>
    by standard (auto intro: trans_equiv trans_less simp: greater_iff_sym_less)
qed

lift_definition key :: \<open>('b \<Rightarrow> 'a) \<Rightarrow> 'a comparator \<Rightarrow> 'b comparator\<close>
  is \<open>\<lambda>f cmp a b. cmp (f a) (f b)\<close>
proof -
  fix cmp :: \<open>'a \<Rightarrow> 'a \<Rightarrow> comp\<close> and f :: \<open>'b \<Rightarrow> 'a\<close>
  assume \<open>comparator cmp\<close>
  then interpret comparator cmp .
  show \<open>comparator (\<lambda>a b. cmp (f a) (f b))\<close>
    by standard (auto intro: trans_equiv trans_less simp: greater_iff_sym_less)
qed


subsection \<open>Direct implementations for linear orders on selected types\<close>

definition comparator_bool :: \<open>bool comparator\<close>
  where [simp, code_abbrev]: \<open>comparator_bool = default\<close>

lemma compare_comparator_bool [code abstract]:
  \<open>compare comparator_bool = (\<lambda>p q.
    if p then if q then Equiv else Greater
    else if q then Less else Equiv)\<close>
  by (auto simp add: fun_eq_iff) (transfer; simp)+

definition raw_comparator_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> comp\<close>
  where [simp]: \<open>raw_comparator_nat = compare default\<close>

lemma default_comparator_nat [simp, code]:
  \<open>raw_comparator_nat (0::nat) 0 = Equiv\<close>
  \<open>raw_comparator_nat (Suc m) 0 = Greater\<close>
  \<open>raw_comparator_nat 0 (Suc n) = Less\<close>
  \<open>raw_comparator_nat (Suc m) (Suc n) = raw_comparator_nat m n\<close>
  by (transfer; simp)+

definition comparator_nat :: \<open>nat comparator\<close>
  where [simp, code_abbrev]: \<open>comparator_nat = default\<close>

lemma compare_comparator_nat [code abstract]:
  \<open>compare comparator_nat = raw_comparator_nat\<close>
  by simp

definition comparator_linordered_group :: \<open>'a::linordered_ab_group_add comparator\<close>
  where [simp, code_abbrev]: \<open>comparator_linordered_group = default\<close>

lemma comparator_linordered_group [code abstract]:
  \<open>compare comparator_linordered_group = (\<lambda>a b.
    let c = a - b in if c < 0 then Less
    else if c = 0 then Equiv else Greater)\<close>
proof (rule ext)+
  fix a b :: 'a
  show \<open>compare comparator_linordered_group a b =
    (let c = a - b in if c < 0 then Less
       else if c = 0 then Equiv else Greater)\<close>
    by (simp add: Let_def not_less) (transfer; auto)
qed

end
