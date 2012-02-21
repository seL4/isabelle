(*  Title:      HOL/Library/Function_Algebras.thy
    Author:     Jeremy Avigad and Kevin Donnelly; Florian Haftmann, TUM
*)

header {* Pointwise instantiation of functions to algebra type classes *}

theory Function_Algebras
imports Main
begin

text {* Pointwise operations *}

instantiation "fun" :: (type, plus) plus
begin

definition "f + g = (\<lambda>x. f x + g x)"
instance ..

end

instantiation "fun" :: (type, zero) zero
begin

definition "0 = (\<lambda>x. 0)"
instance ..

end

instantiation "fun" :: (type, times) times
begin

definition "f * g = (\<lambda>x. f x * g x)"
instance ..

end

instantiation "fun" :: (type, one) one
begin

definition "1 = (\<lambda>x. 1)"
instance ..

end


text {* Additive structures *}

instance "fun" :: (type, semigroup_add) semigroup_add
  by default (simp add: plus_fun_def add.assoc)

instance "fun" :: (type, cancel_semigroup_add) cancel_semigroup_add
  by default (simp_all add: plus_fun_def fun_eq_iff)

instance "fun" :: (type, ab_semigroup_add) ab_semigroup_add
  by default (simp add: plus_fun_def add.commute)

instance "fun" :: (type, cancel_ab_semigroup_add) cancel_ab_semigroup_add
  by default simp

instance "fun" :: (type, monoid_add) monoid_add
  by default (simp_all add: plus_fun_def zero_fun_def)

instance "fun" :: (type, comm_monoid_add) comm_monoid_add
  by default simp

instance "fun" :: (type, cancel_comm_monoid_add) cancel_comm_monoid_add ..

instance "fun" :: (type, group_add) group_add
  by default
    (simp_all add: plus_fun_def zero_fun_def fun_Compl_def fun_diff_def diff_minus)

instance "fun" :: (type, ab_group_add) ab_group_add
  by default (simp_all add: diff_minus)


text {* Multiplicative structures *}

instance "fun" :: (type, semigroup_mult) semigroup_mult
  by default (simp add: times_fun_def mult.assoc)

instance "fun" :: (type, ab_semigroup_mult) ab_semigroup_mult
  by default (simp add: times_fun_def mult.commute)

instance "fun" :: (type, ab_semigroup_idem_mult) ab_semigroup_idem_mult
  by default (simp add: times_fun_def)

instance "fun" :: (type, monoid_mult) monoid_mult
  by default (simp_all add: times_fun_def one_fun_def)

instance "fun" :: (type, comm_monoid_mult) comm_monoid_mult
  by default simp


text {* Misc *}

instance "fun" :: (type, "Rings.dvd") "Rings.dvd" ..

instance "fun" :: (type, mult_zero) mult_zero
  by default (simp_all add: zero_fun_def times_fun_def)

instance "fun" :: (type, zero_neq_one) zero_neq_one
  by default (simp add: zero_fun_def one_fun_def fun_eq_iff)


text {* Ring structures *}

instance "fun" :: (type, semiring) semiring
  by default (simp_all add: plus_fun_def times_fun_def algebra_simps)

instance "fun" :: (type, comm_semiring) comm_semiring
  by default (simp add: plus_fun_def times_fun_def algebra_simps)

instance "fun" :: (type, semiring_0) semiring_0 ..

instance "fun" :: (type, comm_semiring_0) comm_semiring_0 ..

instance "fun" :: (type, semiring_0_cancel) semiring_0_cancel ..

instance "fun" :: (type, comm_semiring_0_cancel) comm_semiring_0_cancel ..

instance "fun" :: (type, semiring_1) semiring_1 ..

lemma of_nat_fun: "of_nat n = (\<lambda>x::'a. of_nat n)"
proof -
  have comp: "comp = (\<lambda>f g x. f (g x))"
    by (rule ext)+ simp
  have plus_fun: "plus = (\<lambda>f g x. f x + g x)"
    by (rule ext, rule ext) (fact plus_fun_def)
  have "of_nat n = (comp (plus (1::'b)) ^^ n) (\<lambda>x::'a. 0)"
    by (simp add: of_nat_def plus_fun zero_fun_def one_fun_def comp)
  also have "... = comp ((plus 1) ^^ n) (\<lambda>x::'a. 0)"
    by (simp only: comp_funpow)
  finally show ?thesis by (simp add: of_nat_def comp)
qed

instance "fun" :: (type, comm_semiring_1) comm_semiring_1 ..

instance "fun" :: (type, semiring_1_cancel) semiring_1_cancel ..

instance "fun" :: (type, comm_semiring_1_cancel) comm_semiring_1_cancel ..

instance "fun" :: (type, semiring_char_0) semiring_char_0
proof
  from inj_of_nat have "inj (\<lambda>n (x::'a). of_nat n :: 'b)"
    by (rule inj_fun)
  then have "inj (\<lambda>n. of_nat n :: 'a \<Rightarrow> 'b)"
    by (simp add: of_nat_fun)
  then show "inj (of_nat :: nat \<Rightarrow> 'a \<Rightarrow> 'b)" .
qed

instance "fun" :: (type, ring) ring ..

instance "fun" :: (type, comm_ring) comm_ring ..

instance "fun" :: (type, ring_1) ring_1 ..

instance "fun" :: (type, comm_ring_1) comm_ring_1 ..

instance "fun" :: (type, ring_char_0) ring_char_0 ..


text {* Ordereded structures *}

instance "fun" :: (type, ordered_ab_semigroup_add) ordered_ab_semigroup_add
  by default (auto simp add: plus_fun_def le_fun_def intro: add_left_mono)

instance "fun" :: (type, ordered_cancel_ab_semigroup_add) ordered_cancel_ab_semigroup_add ..

instance "fun" :: (type, ordered_ab_semigroup_add_imp_le) ordered_ab_semigroup_add_imp_le
  by default (simp add: plus_fun_def le_fun_def)

instance "fun" :: (type, ordered_comm_monoid_add) ordered_comm_monoid_add ..

instance "fun" :: (type, ordered_ab_group_add) ordered_ab_group_add ..

instance "fun" :: (type, ordered_semiring) ordered_semiring
  by default
    (auto simp add: zero_fun_def times_fun_def le_fun_def intro: mult_left_mono mult_right_mono)

instance "fun" :: (type, ordered_comm_semiring) ordered_comm_semiring
  by default (fact mult_left_mono)

instance "fun" :: (type, ordered_cancel_semiring) ordered_cancel_semiring ..

instance "fun" :: (type, ordered_cancel_comm_semiring) ordered_cancel_comm_semiring ..

instance "fun" :: (type, ordered_ring) ordered_ring ..

instance "fun" :: (type, ordered_comm_ring) ordered_comm_ring ..


lemmas func_plus = plus_fun_def
lemmas func_zero = zero_fun_def
lemmas func_times = times_fun_def
lemmas func_one = one_fun_def

end
