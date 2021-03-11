(*  Author:     Steven Obua, TU Muenchen *)

section \<open>Various algebraic structures combined with a lattice\<close>

theory Lattice_Algebras
  imports Complex_Main
begin

class semilattice_inf_ab_group_add = ordered_ab_group_add + semilattice_inf
begin

lemma add_inf_distrib_left: "a + inf b c = inf (a + b) (a + c)"
  apply (rule order.antisym)
   apply (simp_all add: le_infI)
  apply (rule add_le_imp_le_left [of "uminus a"])
  apply (simp only: add.assoc [symmetric], simp add: diff_le_eq add.commute)
  done

lemma add_inf_distrib_right: "inf a b + c = inf (a + c) (b + c)"
proof -
  have "c + inf a b = inf (c + a) (c + b)"
    by (simp add: add_inf_distrib_left)
  then show ?thesis
    by (simp add: add.commute)
qed

end

class semilattice_sup_ab_group_add = ordered_ab_group_add + semilattice_sup
begin

lemma add_sup_distrib_left: "a + sup b c = sup (a + b) (a + c)"
  apply (rule order.antisym)
   apply (rule add_le_imp_le_left [of "uminus a"])
   apply (simp only: add.assoc [symmetric], simp)
   apply (simp add: le_diff_eq add.commute)
  apply (rule le_supI)
   apply (rule add_le_imp_le_left [of "a"], simp only: add.assoc[symmetric], simp)+
  done

lemma add_sup_distrib_right: "sup a b + c = sup (a + c) (b + c)"
proof -
  have "c + sup a b = sup (c+a) (c+b)"
    by (simp add: add_sup_distrib_left)
  then show ?thesis
    by (simp add: add.commute)
qed

end

class lattice_ab_group_add = ordered_ab_group_add + lattice
begin

subclass semilattice_inf_ab_group_add ..
subclass semilattice_sup_ab_group_add ..

lemmas add_sup_inf_distribs =
  add_inf_distrib_right add_inf_distrib_left add_sup_distrib_right add_sup_distrib_left

lemma inf_eq_neg_sup: "inf a b = - sup (- a) (- b)"
proof (rule inf_unique)
  fix a b c :: 'a
  show "- sup (- a) (- b) \<le> a"
    by (rule add_le_imp_le_right [of _ "sup (uminus a) (uminus b)"])
      (simp, simp add: add_sup_distrib_left)
  show "- sup (-a) (-b) \<le> b"
    by (rule add_le_imp_le_right [of _ "sup (uminus a) (uminus b)"])
      (simp, simp add: add_sup_distrib_left)
  assume "a \<le> b" "a \<le> c"
  then show "a \<le> - sup (-b) (-c)"
    by (subst neg_le_iff_le [symmetric]) (simp add: le_supI)
qed

lemma sup_eq_neg_inf: "sup a b = - inf (- a) (- b)"
proof (rule sup_unique)
  fix a b c :: 'a
  show "a \<le> - inf (- a) (- b)"
    by (rule add_le_imp_le_right [of _ "inf (uminus a) (uminus b)"])
      (simp, simp add: add_inf_distrib_left)
  show "b \<le> - inf (- a) (- b)"
    by (rule add_le_imp_le_right [of _ "inf (uminus a) (uminus b)"])
      (simp, simp add: add_inf_distrib_left)
  show "- inf (- a) (- b) \<le> c" if "a \<le> c" "b \<le> c"
    using that by (subst neg_le_iff_le [symmetric]) (simp add: le_infI)
qed

lemma neg_inf_eq_sup: "- inf a b = sup (- a) (- b)"
  by (simp add: inf_eq_neg_sup)

lemma diff_inf_eq_sup: "a - inf b c = a + sup (- b) (- c)"
  using neg_inf_eq_sup [of b c, symmetric] by simp

lemma neg_sup_eq_inf: "- sup a b = inf (- a) (- b)"
  by (simp add: sup_eq_neg_inf)

lemma diff_sup_eq_inf: "a - sup b c = a + inf (- b) (- c)"
  using neg_sup_eq_inf [of b c, symmetric] by simp

lemma add_eq_inf_sup: "a + b = sup a b + inf a b"
proof -
  have "0 = - inf 0 (a - b) + inf (a - b) 0"
    by (simp add: inf_commute)
  then have "0 = sup 0 (b - a) + inf (a - b) 0"
    by (simp add: inf_eq_neg_sup)
  then have "0 = (- a + sup a b) + (inf a b + (- b))"
    by (simp only: add_sup_distrib_left add_inf_distrib_right) simp
  then show ?thesis
    by (simp add: algebra_simps)
qed


subsection \<open>Positive Part, Negative Part, Absolute Value\<close>

definition nprt :: "'a \<Rightarrow> 'a"
  where "nprt x = inf x 0"

definition pprt :: "'a \<Rightarrow> 'a"
  where "pprt x = sup x 0"

lemma pprt_neg: "pprt (- x) = - nprt x"
proof -
  have "sup (- x) 0 = sup (- x) (- 0)"
    by (simp only: minus_zero)
  also have "\<dots> = - inf x 0"
    by (simp only: neg_inf_eq_sup)
  finally have "sup (- x) 0 = - inf x 0" .
  then show ?thesis
    by (simp only: pprt_def nprt_def)
qed

lemma nprt_neg: "nprt (- x) = - pprt x"
proof -
  from pprt_neg have "pprt (- (- x)) = - nprt (- x)" .
  then have "pprt x = - nprt (- x)" by simp
  then show ?thesis by simp
qed

lemma prts: "a = pprt a + nprt a"
  by (simp add: pprt_def nprt_def flip: add_eq_inf_sup)

lemma zero_le_pprt[simp]: "0 \<le> pprt a"
  by (simp add: pprt_def)

lemma nprt_le_zero[simp]: "nprt a \<le> 0"
  by (simp add: nprt_def)

lemma le_eq_neg: "a \<le> - b \<longleftrightarrow> a + b \<le> 0"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  show ?rhs
    by (rule add_le_imp_le_right[of _ "uminus b" _]) (simp add: add.assoc \<open>?lhs\<close>)
next
  assume ?rhs
  show ?lhs
    by (rule add_le_imp_le_right[of _ "b" _]) (simp add: \<open>?rhs\<close>)
qed

lemma pprt_0[simp]: "pprt 0 = 0" by (simp add: pprt_def)
lemma nprt_0[simp]: "nprt 0 = 0" by (simp add: nprt_def)

lemma pprt_eq_id [simp, no_atp]: "0 \<le> x \<Longrightarrow> pprt x = x"
  by (simp add: pprt_def sup_absorb1)

lemma nprt_eq_id [simp, no_atp]: "x \<le> 0 \<Longrightarrow> nprt x = x"
  by (simp add: nprt_def inf_absorb1)

lemma pprt_eq_0 [simp, no_atp]: "x \<le> 0 \<Longrightarrow> pprt x = 0"
  by (simp add: pprt_def sup_absorb2)

lemma nprt_eq_0 [simp, no_atp]: "0 \<le> x \<Longrightarrow> nprt x = 0"
  by (simp add: nprt_def inf_absorb2)

lemma sup_0_imp_0:
  assumes "sup a (- a) = 0"
  shows "a = 0"
proof -
  have pos: "0 \<le> a" if "sup a (- a) = 0" for a :: 'a
  proof -
    from that have "sup a (- a) + a = a"
      by simp
    then have "sup (a + a) 0 = a"
      by (simp add: add_sup_distrib_right)
    then have "sup (a + a) 0 \<le> a"
      by simp
    then show ?thesis
      by (blast intro: order_trans inf_sup_ord)
  qed
  from assms have **: "sup (-a) (-(-a)) = 0"
    by (simp add: sup_commute)
  from pos[OF assms] pos[OF **] show "a = 0"
    by simp
qed

lemma inf_0_imp_0: "inf a (- a) = 0 \<Longrightarrow> a = 0"
  apply (simp add: inf_eq_neg_sup)
  apply (simp add: sup_commute)
  apply (erule sup_0_imp_0)
  done

lemma inf_0_eq_0 [simp, no_atp]: "inf a (- a) = 0 \<longleftrightarrow> a = 0"
  apply (rule iffI)
   apply (erule inf_0_imp_0)
  apply simp
  done

lemma sup_0_eq_0 [simp, no_atp]: "sup a (- a) = 0 \<longleftrightarrow> a = 0"
  apply (rule iffI)
   apply (erule sup_0_imp_0)
  apply simp
  done

lemma zero_le_double_add_iff_zero_le_single_add [simp]: "0 \<le> a + a \<longleftrightarrow> 0 \<le> a"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show ?rhs if ?lhs
  proof -
    from that have a: "inf (a + a) 0 = 0"
      by (simp add: inf_commute inf_absorb1)
    have "inf a 0 + inf a 0 = inf (inf (a + a) 0) a"  (is "?l = _")
      by (simp add: add_sup_inf_distribs inf_aci)
    then have "?l = 0 + inf a 0"
      by (simp add: a, simp add: inf_commute)
    then have "inf a 0 = 0"
      by (simp only: add_right_cancel)
    then show ?thesis
      unfolding le_iff_inf by (simp add: inf_commute)
  qed
  show ?lhs if ?rhs
    by (simp add: add_mono[OF that that, simplified])
qed

lemma double_zero [simp]: "a + a = 0 \<longleftrightarrow> a = 0"
  using add_nonneg_eq_0_iff order.eq_iff by auto

lemma zero_less_double_add_iff_zero_less_single_add [simp]: "0 < a + a \<longleftrightarrow> 0 < a"
  by (meson le_less_trans less_add_same_cancel2 less_le_not_le
      zero_le_double_add_iff_zero_le_single_add)

lemma double_add_le_zero_iff_single_add_le_zero [simp]: "a + a \<le> 0 \<longleftrightarrow> a \<le> 0"
proof -
  have "a + a \<le> 0 \<longleftrightarrow> 0 \<le> - (a + a)"
    by (subst le_minus_iff) simp
  moreover have "\<dots> \<longleftrightarrow> a \<le> 0"
    by (simp only: minus_add_distrib zero_le_double_add_iff_zero_le_single_add) simp
  ultimately show ?thesis
    by blast
qed

lemma double_add_less_zero_iff_single_less_zero [simp]: "a + a < 0 \<longleftrightarrow> a < 0"
proof -
  have "a + a < 0 \<longleftrightarrow> 0 < - (a + a)"
    by (subst less_minus_iff) simp
  moreover have "\<dots> \<longleftrightarrow> a < 0"
    by (simp only: minus_add_distrib zero_less_double_add_iff_zero_less_single_add) simp
  ultimately show ?thesis
    by blast
qed

declare neg_inf_eq_sup [simp]
  and neg_sup_eq_inf [simp]
  and diff_inf_eq_sup [simp]
  and diff_sup_eq_inf [simp]

lemma le_minus_self_iff: "a \<le> - a \<longleftrightarrow> a \<le> 0"
proof -
  from add_le_cancel_left [of "uminus a" "plus a a" zero]
  have "a \<le> - a \<longleftrightarrow> a + a \<le> 0"
    by (simp flip: add.assoc)
  then show ?thesis
    by simp
qed

lemma minus_le_self_iff: "- a \<le> a \<longleftrightarrow> 0 \<le> a"
proof -
  have "- a \<le> a \<longleftrightarrow> 0 \<le> a + a"
    using add_le_cancel_left [of "uminus a" zero "plus a a"]
    by (simp flip: add.assoc)
  then show ?thesis
    by simp
qed

lemma zero_le_iff_zero_nprt: "0 \<le> a \<longleftrightarrow> nprt a = 0"
  unfolding le_iff_inf by (simp add: nprt_def inf_commute)

lemma le_zero_iff_zero_pprt: "a \<le> 0 \<longleftrightarrow> pprt a = 0"
  unfolding le_iff_sup by (simp add: pprt_def sup_commute)

lemma le_zero_iff_pprt_id: "0 \<le> a \<longleftrightarrow> pprt a = a"
  unfolding le_iff_sup by (simp add: pprt_def sup_commute)

lemma zero_le_iff_nprt_id: "a \<le> 0 \<longleftrightarrow> nprt a = a"
  unfolding le_iff_inf by (simp add: nprt_def inf_commute)

lemma pprt_mono [simp, no_atp]: "a \<le> b \<Longrightarrow> pprt a \<le> pprt b"
  unfolding le_iff_sup by (simp add: pprt_def sup_aci sup_assoc [symmetric, of a])

lemma nprt_mono [simp, no_atp]: "a \<le> b \<Longrightarrow> nprt a \<le> nprt b"
  unfolding le_iff_inf by (simp add: nprt_def inf_aci inf_assoc [symmetric, of a])

end

lemmas add_sup_inf_distribs =
  add_inf_distrib_right add_inf_distrib_left add_sup_distrib_right add_sup_distrib_left


class lattice_ab_group_add_abs = lattice_ab_group_add + abs +
  assumes abs_lattice: "\<bar>a\<bar> = sup a (- a)"
begin

lemma abs_prts: "\<bar>a\<bar> = pprt a - nprt a"
proof -
  have "0 \<le> \<bar>a\<bar>"
  proof -
    have a: "a \<le> \<bar>a\<bar>" and b: "- a \<le> \<bar>a\<bar>"
      by (auto simp add: abs_lattice)
    show ?thesis
      by (rule add_mono [OF a b, simplified])
  qed
  then have "0 \<le> sup a (- a)"
    unfolding abs_lattice .
  then have "sup (sup a (- a)) 0 = sup a (- a)"
    by (rule sup_absorb1)
  then show ?thesis
    by (simp add: add_sup_inf_distribs ac_simps pprt_def nprt_def abs_lattice)
qed

subclass ordered_ab_group_add_abs
proof
  have abs_ge_zero [simp]: "0 \<le> \<bar>a\<bar>" for a
  proof -
    have a: "a \<le> \<bar>a\<bar>" and b: "- a \<le> \<bar>a\<bar>"
      by (auto simp add: abs_lattice)
    show "0 \<le> \<bar>a\<bar>"
      by (rule add_mono [OF a b, simplified])
  qed
  have abs_leI: "a \<le> b \<Longrightarrow> - a \<le> b \<Longrightarrow> \<bar>a\<bar> \<le> b" for a b
    by (simp add: abs_lattice le_supI)
  fix a b
  show "0 \<le> \<bar>a\<bar>"
    by simp
  show "a \<le> \<bar>a\<bar>"
    by (auto simp add: abs_lattice)
  show "\<bar>-a\<bar> = \<bar>a\<bar>"
    by (simp add: abs_lattice sup_commute)
  show "- a \<le> b \<Longrightarrow> \<bar>a\<bar> \<le> b" if "a \<le> b"
    using that by (rule abs_leI)
  show "\<bar>a + b\<bar> \<le> \<bar>a\<bar> + \<bar>b\<bar>"
  proof -
    have g: "\<bar>a\<bar> + \<bar>b\<bar> = sup (a + b) (sup (- a - b) (sup (- a + b) (a + (- b))))"
      (is "_ = sup ?m ?n")
      by (simp add: abs_lattice add_sup_inf_distribs ac_simps)
    have a: "a + b \<le> sup ?m ?n"
      by simp
    have b: "- a - b \<le> ?n"
      by simp
    have c: "?n \<le> sup ?m ?n"
      by simp
    from b c have d: "- a - b \<le> sup ?m ?n"
      by (rule order_trans)
    have e: "- a - b = - (a + b)"
      by simp
    from a d e have "\<bar>a + b\<bar> \<le> sup ?m ?n"
      apply -
      apply (drule abs_leI)
       apply (simp_all only: algebra_simps minus_add)
      apply (metis add_uminus_conv_diff d sup_commute uminus_add_conv_diff)
      done
    with g[symmetric] show ?thesis by simp
  qed
qed

end

lemma sup_eq_if:
  fixes a :: "'a::{lattice_ab_group_add,linorder}"
  shows "sup a (- a) = (if a < 0 then - a else a)"
  using add_le_cancel_right [of a a "- a", symmetric, simplified]
    and add_le_cancel_right [of "-a" a a, symmetric, simplified]
  by (auto simp: sup_max max.absorb1 max.absorb2)

lemma abs_if_lattice:
  fixes a :: "'a::{lattice_ab_group_add_abs,linorder}"
  shows "\<bar>a\<bar> = (if a < 0 then - a else a)"
  by auto

lemma estimate_by_abs:
  fixes a b c :: "'a::lattice_ab_group_add_abs"
  assumes "a + b \<le> c"
  shows "a \<le> c + \<bar>b\<bar>"
proof -
  from assms have "a \<le> c + (- b)"
    by (simp add: algebra_simps)
  have "- b \<le> \<bar>b\<bar>"
    by (rule abs_ge_minus_self)
  then have "c + (- b) \<le> c + \<bar>b\<bar>"
    by (rule add_left_mono)
  with \<open>a \<le> c + (- b)\<close> show ?thesis
    by (rule order_trans)
qed

class lattice_ring = ordered_ring + lattice_ab_group_add_abs
begin

subclass semilattice_inf_ab_group_add ..
subclass semilattice_sup_ab_group_add ..

end

lemma abs_le_mult:
  fixes a b :: "'a::lattice_ring"
  shows "\<bar>a * b\<bar> \<le> \<bar>a\<bar> * \<bar>b\<bar>"
proof -
  let ?x = "pprt a * pprt b - pprt a * nprt b - nprt a * pprt b + nprt a * nprt b"
  let ?y = "pprt a * pprt b + pprt a * nprt b + nprt a * pprt b + nprt a * nprt b"
  have a: "\<bar>a\<bar> * \<bar>b\<bar> = ?x"
    by (simp only: abs_prts[of a] abs_prts[of b] algebra_simps)
  have bh: "u = a \<Longrightarrow> v = b \<Longrightarrow>
            u * v = pprt a * pprt b + pprt a * nprt b +
                    nprt a * pprt b + nprt a * nprt b" for u v :: 'a
    apply (subst prts[of u], subst prts[of v])
    apply (simp add: algebra_simps)
    done
  note b = this[OF refl[of a] refl[of b]]
  have xy: "- ?x \<le> ?y"
    apply simp
    apply (metis (full_types) add_increasing add_uminus_conv_diff
      lattice_ab_group_add_class.minus_le_self_iff minus_add_distrib mult_nonneg_nonneg
      mult_nonpos_nonpos nprt_le_zero zero_le_pprt)
    done
  have yx: "?y \<le> ?x"
    apply simp
    apply (metis (full_types) add_nonpos_nonpos add_uminus_conv_diff
      lattice_ab_group_add_class.le_minus_self_iff minus_add_distrib mult_nonneg_nonpos
      mult_nonpos_nonneg nprt_le_zero zero_le_pprt)
    done
  have i1: "a * b \<le> \<bar>a\<bar> * \<bar>b\<bar>"
    by (simp only: a b yx)
  have i2: "- (\<bar>a\<bar> * \<bar>b\<bar>) \<le> a * b"
    by (simp only: a b xy)
  show ?thesis
    apply (rule abs_leI)
    apply (simp add: i1)
    apply (simp add: i2[simplified minus_le_iff])
    done
qed

instance lattice_ring \<subseteq> ordered_ring_abs
proof
  fix a b :: "'a::lattice_ring"
  assume a: "(0 \<le> a \<or> a \<le> 0) \<and> (0 \<le> b \<or> b \<le> 0)"
  show "\<bar>a * b\<bar> = \<bar>a\<bar> * \<bar>b\<bar>"
  proof -
    have s: "(0 \<le> a * b) \<or> (a * b \<le> 0)"
      apply auto
      apply (rule_tac split_mult_pos_le)
      apply (rule_tac contrapos_np[of "a * b \<le> 0"])
      apply simp
      apply (rule_tac split_mult_neg_le)
      using a
      apply blast
      done
    have mulprts: "a * b = (pprt a + nprt a) * (pprt b + nprt b)"
      by (simp flip: prts)
    show ?thesis
    proof (cases "0 \<le> a * b")
      case True
      then show ?thesis
        apply (simp_all add: mulprts abs_prts)
        using a
        apply (auto simp add:
          algebra_simps
          iffD1[OF zero_le_iff_zero_nprt] iffD1[OF le_zero_iff_zero_pprt]
          iffD1[OF le_zero_iff_pprt_id] iffD1[OF zero_le_iff_nprt_id])
        apply(drule (1) mult_nonneg_nonpos[of a b], simp)
        apply(drule (1) mult_nonneg_nonpos2[of b a], simp)
        done
    next
      case False
      with s have "a * b \<le> 0"
        by simp
      then show ?thesis
        apply (simp_all add: mulprts abs_prts)
        apply (insert a)
        apply (auto simp add: algebra_simps)
        apply(drule (1) mult_nonneg_nonneg[of a b],simp)
        apply(drule (1) mult_nonpos_nonpos[of a b],simp)
        done
    qed
  qed
qed

lemma mult_le_prts:
  fixes a b :: "'a::lattice_ring"
  assumes "a1 \<le> a"
    and "a \<le> a2"
    and "b1 \<le> b"
    and "b \<le> b2"
  shows "a * b \<le>
    pprt a2 * pprt b2 + pprt a1 * nprt b2 + nprt a2 * pprt b1 + nprt a1 * nprt b1"
proof -
  have "a * b = (pprt a + nprt a) * (pprt b + nprt b)"
    by (subst prts[symmetric])+ simp
  then have "a * b = pprt a * pprt b + pprt a * nprt b + nprt a * pprt b + nprt a * nprt b"
    by (simp add: algebra_simps)
  moreover have "pprt a * pprt b \<le> pprt a2 * pprt b2"
    by (simp_all add: assms mult_mono)
  moreover have "pprt a * nprt b \<le> pprt a1 * nprt b2"
  proof -
    have "pprt a * nprt b \<le> pprt a * nprt b2"
      by (simp add: mult_left_mono assms)
    moreover have "pprt a * nprt b2 \<le> pprt a1 * nprt b2"
      by (simp add: mult_right_mono_neg assms)
    ultimately show ?thesis
      by simp
  qed
  moreover have "nprt a * pprt b \<le> nprt a2 * pprt b1"
  proof -
    have "nprt a * pprt b \<le> nprt a2 * pprt b"
      by (simp add: mult_right_mono assms)
    moreover have "nprt a2 * pprt b \<le> nprt a2 * pprt b1"
      by (simp add: mult_left_mono_neg assms)
    ultimately show ?thesis
      by simp
  qed
  moreover have "nprt a * nprt b \<le> nprt a1 * nprt b1"
  proof -
    have "nprt a * nprt b \<le> nprt a * nprt b1"
      by (simp add: mult_left_mono_neg assms)
    moreover have "nprt a * nprt b1 \<le> nprt a1 * nprt b1"
      by (simp add: mult_right_mono_neg assms)
    ultimately show ?thesis
      by simp
  qed
  ultimately show ?thesis
    by - (rule add_mono | simp)+
qed

lemma mult_ge_prts:
  fixes a b :: "'a::lattice_ring"
  assumes "a1 \<le> a"
    and "a \<le> a2"
    and "b1 \<le> b"
    and "b \<le> b2"
  shows "a * b \<ge>
    nprt a1 * pprt b2 + nprt a2 * nprt b2 + pprt a1 * pprt b1 + pprt a2 * nprt b1"
proof -
  from assms have a1: "- a2 \<le> -a"
    by auto
  from assms have a2: "- a \<le> -a1"
    by auto
  from mult_le_prts[of "- a2" "- a" "- a1" "b1" b "b2",
    OF a1 a2 assms(3) assms(4), simplified nprt_neg pprt_neg]
  have le: "- (a * b) \<le>
    - nprt a1 * pprt b2 + - nprt a2 * nprt b2 +
    - pprt a1 * pprt b1 + - pprt a2 * nprt b1"
    by simp
  then have "- (- nprt a1 * pprt b2 + - nprt a2 * nprt b2 +
      - pprt a1 * pprt b1 + - pprt a2 * nprt b1) \<le> a * b"
    by (simp only: minus_le_iff)
  then show ?thesis
    by (simp add: algebra_simps)
qed

instance int :: lattice_ring
proof
  show "\<bar>k\<bar> = sup k (- k)" for k :: int
    by (auto simp add: sup_int_def)
qed

instance real :: lattice_ring
proof
  show "\<bar>a\<bar> = sup a (- a)" for a :: real
    by (auto simp add: sup_real_def)
qed

end
