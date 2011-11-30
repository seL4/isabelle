(*  Title:      HOL/Library/Saturated.thy
    Author:     Brian Huffman
    Author:     Peter Gammie
    Author:     Florian Haftmann
*)

header {* Saturated arithmetic *}

theory Saturated
imports Main "~~/src/HOL/Library/Numeral_Type" "~~/src/HOL/Word/Type_Length"
begin

subsection {* The type of saturated naturals *}

typedef (open) ('a::len) sat = "{.. len_of TYPE('a)}"
  morphisms nat_of Abs_sat
  by auto

lemma sat_eqI:
  "nat_of m = nat_of n \<Longrightarrow> m = n"
  by (simp add: nat_of_inject)

lemma sat_eq_iff:
  "m = n \<longleftrightarrow> nat_of m = nat_of n"
  by (simp add: nat_of_inject)

lemma Abs_sat_nat_of [code abstype]:
  "Abs_sat (nat_of n) = n"
  by (fact nat_of_inverse)

definition Abs_sat' :: "nat \<Rightarrow> 'a::len sat" where
  "Abs_sat' n = Abs_sat (min (len_of TYPE('a)) n)"

lemma nat_of_Abs_sat' [simp]:
  "nat_of (Abs_sat' n :: ('a::len) sat) = min (len_of TYPE('a)) n"
  unfolding Abs_sat'_def by (rule Abs_sat_inverse) simp

lemma nat_of_le_len_of [simp]:
  "nat_of (n :: ('a::len) sat) \<le> len_of TYPE('a)"
  using nat_of [where x = n] by simp

lemma min_len_of_nat_of [simp]:
  "min (len_of TYPE('a)) (nat_of (n::('a::len) sat)) = nat_of n"
  by (rule min_max.inf_absorb2 [OF nat_of_le_len_of])

lemma min_nat_of_len_of [simp]:
  "min (nat_of (n::('a::len) sat)) (len_of TYPE('a)) = nat_of n"
  by (subst min_max.inf.commute) simp

lemma Abs_sat'_nat_of [simp]:
  "Abs_sat' (nat_of n) = n"
  by (simp add: Abs_sat'_def nat_of_inverse)

instantiation sat :: (len) linorder
begin

definition
  less_eq_sat_def: "x \<le> y \<longleftrightarrow> nat_of x \<le> nat_of y"

definition
  less_sat_def: "x < y \<longleftrightarrow> nat_of x < nat_of y"

instance
by default (auto simp add: less_eq_sat_def less_sat_def not_le sat_eq_iff min_max.le_infI1 nat_mult_commute)

end

instantiation sat :: (len) "{minus, comm_semiring_1}"
begin

definition
  "0 = Abs_sat' 0"

definition
  "1 = Abs_sat' 1"

lemma nat_of_zero_sat [simp, code abstract]:
  "nat_of 0 = 0"
  by (simp add: zero_sat_def)

lemma nat_of_one_sat [simp, code abstract]:
  "nat_of 1 = min 1 (len_of TYPE('a))"
  by (simp add: one_sat_def)

definition
  "x + y = Abs_sat' (nat_of x + nat_of y)"

lemma nat_of_plus_sat [simp, code abstract]:
  "nat_of (x + y) = min (nat_of x + nat_of y) (len_of TYPE('a))"
  by (simp add: plus_sat_def)

definition
  "x - y = Abs_sat' (nat_of x - nat_of y)"

lemma nat_of_minus_sat [simp, code abstract]:
  "nat_of (x - y) = nat_of x - nat_of y"
proof -
  from nat_of_le_len_of [of x] have "nat_of x - nat_of y \<le> len_of TYPE('a)" by arith
  then show ?thesis by (simp add: minus_sat_def)
qed

definition
  "x * y = Abs_sat' (nat_of x * nat_of y)"

lemma nat_of_times_sat [simp, code abstract]:
  "nat_of (x * y) = min (nat_of x * nat_of y) (len_of TYPE('a))"
  by (simp add: times_sat_def)

instance proof
  fix a b c :: "('a::len) sat"
  show "a * b * c = a * (b * c)"
  proof(cases "a = 0")
    case True thus ?thesis by (simp add: sat_eq_iff)
  next
    case False show ?thesis
    proof(cases "c = 0")
      case True thus ?thesis by (simp add: sat_eq_iff)
    next
      case False with `a \<noteq> 0` show ?thesis
        by (simp add: sat_eq_iff nat_mult_min_left nat_mult_min_right mult_assoc min_max.inf_assoc min_max.inf_absorb2)
    qed
  qed
next
  fix a :: "('a::len) sat"
  show "1 * a = a"
    apply (simp add: sat_eq_iff)
    apply (metis One_nat_def len_gt_0 less_Suc0 less_zeroE linorder_not_less min_max.le_iff_inf min_nat_of_len_of nat_mult_1_right nat_mult_commute)
    done
next
  fix a b c :: "('a::len) sat"
  show "(a + b) * c = a * c + b * c"
  proof(cases "c = 0")
    case True thus ?thesis by (simp add: sat_eq_iff)
  next
    case False thus ?thesis
      by (simp add: sat_eq_iff nat_mult_min_left add_mult_distrib min_add_distrib_left min_add_distrib_right min_max.inf_assoc min_max.inf_absorb2)
  qed
qed (simp_all add: sat_eq_iff mult.commute)

end

instantiation sat :: (len) ordered_comm_semiring
begin

instance
by default (auto simp add: less_eq_sat_def less_sat_def not_le sat_eq_iff min_max.le_infI1 nat_mult_commute)

end

lemma Abs_sat'_eq_of_nat: "Abs_sat' n = of_nat n"
  by (rule sat_eqI, induct n, simp_all)

abbreviation Sat :: "nat \<Rightarrow> 'a::len sat" where
  "Sat \<equiv> of_nat"

lemma nat_of_Sat [simp]:
  "nat_of (Sat n :: ('a::len) sat) = min (len_of TYPE('a)) n"
  by (rule nat_of_Abs_sat' [unfolded Abs_sat'_eq_of_nat])

instantiation sat :: (len) number_semiring
begin

definition
  number_of_sat_def [code del]: "number_of = Sat \<circ> nat"

instance
  by default (simp add: number_of_sat_def)

end

lemma [code abstract]:
  "nat_of (number_of n :: ('a::len) sat) = min (nat n) (len_of TYPE('a))"
  unfolding number_of_sat_def by simp

instance sat :: (len) finite
proof
  show "finite (UNIV::'a sat set)"
    unfolding type_definition.univ [OF type_definition_sat]
    using finite by simp
qed

instantiation sat :: (len) equal
begin

definition
  "HOL.equal A B \<longleftrightarrow> nat_of A = nat_of B"

instance proof
qed (simp add: equal_sat_def nat_of_inject)

end

instantiation sat :: (len) "{bounded_lattice, distrib_lattice}"
begin

definition
  "(inf :: 'a sat \<Rightarrow> 'a sat \<Rightarrow> 'a sat) = min"

definition
  "(sup :: 'a sat \<Rightarrow> 'a sat \<Rightarrow> 'a sat) = max"

definition
  "bot = (0 :: 'a sat)"

definition
  "top = Sat (len_of TYPE('a))"

instance proof
qed (simp_all add: inf_sat_def sup_sat_def bot_sat_def top_sat_def min_max.sup_inf_distrib1,
  simp_all add: less_eq_sat_def)

end

instantiation sat :: (len) complete_lattice
begin

definition
  "Inf (A :: 'a sat set) = fold min top A"

definition
  "Sup (A :: 'a sat set) = fold max bot A"

instance proof
  fix x :: "'a sat"
  fix A :: "'a sat set"
  note finite
  moreover assume "x \<in> A"
  ultimately have "fold min top A \<le> min x top" by (rule min_max.fold_inf_le_inf)
  then show "Inf A \<le> x" by (simp add: Inf_sat_def)
next
  fix z :: "'a sat"
  fix A :: "'a sat set"
  note finite
  moreover assume z: "\<And>x. x \<in> A \<Longrightarrow> z \<le> x"
  ultimately have "min z top \<le> fold min top A" by (blast intro: min_max.inf_le_fold_inf)
  then show "z \<le> Inf A" by (simp add: Inf_sat_def min_def)
next
  fix x :: "'a sat"
  fix A :: "'a sat set"
  note finite
  moreover assume "x \<in> A"
  ultimately have "max x bot \<le> fold max bot A" by (rule min_max.sup_le_fold_sup)
  then show "x \<le> Sup A" by (simp add: Sup_sat_def)
next
  fix z :: "'a sat"
  fix A :: "'a sat set"
  note finite
  moreover assume z: "\<And>x. x \<in> A \<Longrightarrow> x \<le> z"
  ultimately have "fold max bot A \<le> max z bot" by (blast intro: min_max.fold_sup_le_sup)
  then show "Sup A \<le> z" by (simp add: Sup_sat_def max_def bot_unique)
qed

end

end
