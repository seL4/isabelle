(* Author: Steven Obua, TU Muenchen *)

header {* Various algebraic structures combined with a lattice *}

theory Lattice_Algebras
imports Complex_Main
begin

class semilattice_inf_ab_group_add = ordered_ab_group_add + semilattice_inf
begin

lemma add_inf_distrib_left:
  "a + inf b c = inf (a + b) (a + c)"
apply (rule antisym)
apply (simp_all add: le_infI)
apply (rule add_le_imp_le_left [of "uminus a"])
apply (simp only: add_assoc [symmetric], simp)
apply rule
apply (rule add_le_imp_le_left[of "a"], simp only: add_assoc[symmetric], simp)+
done

lemma add_inf_distrib_right:
  "inf a b + c = inf (a + c) (b + c)"
proof -
  have "c + inf a b = inf (c+a) (c+b)" by (simp add: add_inf_distrib_left)
  thus ?thesis by (simp add: add_commute)
qed

end

class semilattice_sup_ab_group_add = ordered_ab_group_add + semilattice_sup
begin

lemma add_sup_distrib_left:
  "a + sup b c = sup (a + b) (a + c)" 
apply (rule antisym)
apply (rule add_le_imp_le_left [of "uminus a"])
apply (simp only: add_assoc[symmetric], simp)
apply rule
apply (rule add_le_imp_le_left [of "a"], simp only: add_assoc[symmetric], simp)+
apply (rule le_supI)
apply (simp_all)
done

lemma add_sup_distrib_right:
  "sup a b + c = sup (a+c) (b+c)"
proof -
  have "c + sup a b = sup (c+a) (c+b)" by (simp add: add_sup_distrib_left)
  thus ?thesis by (simp add: add_commute)
qed

end

class lattice_ab_group_add = ordered_ab_group_add + lattice
begin

subclass semilattice_inf_ab_group_add ..
subclass semilattice_sup_ab_group_add ..

lemmas add_sup_inf_distribs = add_inf_distrib_right add_inf_distrib_left add_sup_distrib_right add_sup_distrib_left

lemma inf_eq_neg_sup: "inf a b = - sup (-a) (-b)"
proof (rule inf_unique)
  fix a b :: 'a
  show "- sup (-a) (-b) \<le> a"
    by (rule add_le_imp_le_right [of _ "sup (uminus a) (uminus b)"])
      (simp, simp add: add_sup_distrib_left)
next
  fix a b :: 'a
  show "- sup (-a) (-b) \<le> b"
    by (rule add_le_imp_le_right [of _ "sup (uminus a) (uminus b)"])
      (simp, simp add: add_sup_distrib_left)
next
  fix a b c :: 'a
  assume "a \<le> b" "a \<le> c"
  then show "a \<le> - sup (-b) (-c)" by (subst neg_le_iff_le [symmetric])
    (simp add: le_supI)
qed
  
lemma sup_eq_neg_inf: "sup a b = - inf (-a) (-b)"
proof (rule sup_unique)
  fix a b :: 'a
  show "a \<le> - inf (-a) (-b)"
    by (rule add_le_imp_le_right [of _ "inf (uminus a) (uminus b)"])
      (simp, simp add: add_inf_distrib_left)
next
  fix a b :: 'a
  show "b \<le> - inf (-a) (-b)"
    by (rule add_le_imp_le_right [of _ "inf (uminus a) (uminus b)"])
      (simp, simp add: add_inf_distrib_left)
next
  fix a b c :: 'a
  assume "a \<le> c" "b \<le> c"
  then show "- inf (-a) (-b) \<le> c" by (subst neg_le_iff_le [symmetric])
    (simp add: le_infI)
qed

lemma neg_inf_eq_sup: "- inf a b = sup (-a) (-b)"
by (simp add: inf_eq_neg_sup)

lemma neg_sup_eq_inf: "- sup a b = inf (-a) (-b)"
by (simp add: sup_eq_neg_inf)

lemma add_eq_inf_sup: "a + b = sup a b + inf a b"
proof -
  have "0 = - inf 0 (a-b) + inf (a-b) 0" by (simp add: inf_commute)
  hence "0 = sup 0 (b-a) + inf (a-b) 0" by (simp add: inf_eq_neg_sup)
  hence "0 = (-a + sup a b) + (inf a b + (-b))"
    by (simp add: add_sup_distrib_left add_inf_distrib_right)
       (simp add: algebra_simps)
  thus ?thesis by (simp add: algebra_simps)
qed

subsection {* Positive Part, Negative Part, Absolute Value *}

definition
  nprt :: "'a \<Rightarrow> 'a" where
  "nprt x = inf x 0"

definition
  pprt :: "'a \<Rightarrow> 'a" where
  "pprt x = sup x 0"

lemma pprt_neg: "pprt (- x) = - nprt x"
proof -
  have "sup (- x) 0 = sup (- x) (- 0)" unfolding minus_zero ..
  also have "\<dots> = - inf x 0" unfolding neg_inf_eq_sup ..
  finally have "sup (- x) 0 = - inf x 0" .
  then show ?thesis unfolding pprt_def nprt_def .
qed

lemma nprt_neg: "nprt (- x) = - pprt x"
proof -
  from pprt_neg have "pprt (- (- x)) = - nprt (- x)" .
  then have "pprt x = - nprt (- x)" by simp
  then show ?thesis by simp
qed

lemma prts: "a = pprt a + nprt a"
by (simp add: pprt_def nprt_def add_eq_inf_sup[symmetric])

lemma zero_le_pprt[simp]: "0 \<le> pprt a"
by (simp add: pprt_def)

lemma nprt_le_zero[simp]: "nprt a \<le> 0"
by (simp add: nprt_def)

lemma le_eq_neg: "a \<le> - b \<longleftrightarrow> a + b \<le> 0" (is "?l = ?r")
proof -
  have a: "?l \<longrightarrow> ?r"
    apply (auto)
    apply (rule add_le_imp_le_right[of _ "uminus b" _])
    apply (simp add: add_assoc)
    done
  have b: "?r \<longrightarrow> ?l"
    apply (auto)
    apply (rule add_le_imp_le_right[of _ "b" _])
    apply (simp)
    done
  from a b show ?thesis by blast
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

lemma sup_0_imp_0: "sup a (- a) = 0 \<Longrightarrow> a = 0"
proof -
  {
    fix a::'a
    assume hyp: "sup a (-a) = 0"
    hence "sup a (-a) + a = a" by (simp)
    hence "sup (a+a) 0 = a" by (simp add: add_sup_distrib_right) 
    hence "sup (a+a) 0 <= a" by (simp)
    hence "0 <= a" by (blast intro: order_trans inf_sup_ord)
  }
  note p = this
  assume hyp:"sup a (-a) = 0"
  hence hyp2:"sup (-a) (-(-a)) = 0" by (simp add: sup_commute)
  from p[OF hyp] p[OF hyp2] show "a = 0" by simp
qed

lemma inf_0_imp_0: "inf a (-a) = 0 \<Longrightarrow> a = 0"
apply (simp add: inf_eq_neg_sup)
apply (simp add: sup_commute)
apply (erule sup_0_imp_0)
done

lemma inf_0_eq_0 [simp, no_atp]: "inf a (- a) = 0 \<longleftrightarrow> a = 0"
by (rule, erule inf_0_imp_0) simp

lemma sup_0_eq_0 [simp, no_atp]: "sup a (- a) = 0 \<longleftrightarrow> a = 0"
by (rule, erule sup_0_imp_0) simp

lemma zero_le_double_add_iff_zero_le_single_add [simp]:
  "0 \<le> a + a \<longleftrightarrow> 0 \<le> a"
proof
  assume "0 <= a + a"
  hence a:"inf (a+a) 0 = 0" by (simp add: inf_commute inf_absorb1)
  have "(inf a 0)+(inf a 0) = inf (inf (a+a) 0) a" (is "?l=_")
    by (simp add: add_sup_inf_distribs inf_aci)
  hence "?l = 0 + inf a 0" by (simp add: a, simp add: inf_commute)
  hence "inf a 0 = 0" by (simp only: add_right_cancel)
  then show "0 <= a" unfolding le_iff_inf by (simp add: inf_commute)
next
  assume a: "0 <= a"
  show "0 <= a + a" by (simp add: add_mono[OF a a, simplified])
qed

lemma double_zero [simp]:
  "a + a = 0 \<longleftrightarrow> a = 0"
proof
  assume assm: "a + a = 0"
  then have "a + a + - a = - a" by simp
  then have "a + (a + - a) = - a" by (simp only: add_assoc)
  then have a: "- a = a" by simp
  show "a = 0" apply (rule antisym)
  apply (unfold neg_le_iff_le [symmetric, of a])
  unfolding a apply simp
  unfolding zero_le_double_add_iff_zero_le_single_add [symmetric, of a]
  unfolding assm unfolding le_less apply simp_all done
next
  assume "a = 0" then show "a + a = 0" by simp
qed

lemma zero_less_double_add_iff_zero_less_single_add [simp]:
  "0 < a + a \<longleftrightarrow> 0 < a"
proof (cases "a = 0")
  case True then show ?thesis by auto
next
  case False then show ?thesis (*FIXME tune proof*)
  unfolding less_le apply simp apply rule
  apply clarify
  apply rule
  apply assumption
  apply (rule notI)
  unfolding double_zero [symmetric, of a] apply simp
  done
qed

lemma double_add_le_zero_iff_single_add_le_zero [simp]:
  "a + a \<le> 0 \<longleftrightarrow> a \<le> 0" 
proof -
  have "a + a \<le> 0 \<longleftrightarrow> 0 \<le> - (a + a)" by (subst le_minus_iff, simp)
  moreover have "\<dots> \<longleftrightarrow> a \<le> 0" by simp
  ultimately show ?thesis by blast
qed

lemma double_add_less_zero_iff_single_less_zero [simp]:
  "a + a < 0 \<longleftrightarrow> a < 0"
proof -
  have "a + a < 0 \<longleftrightarrow> 0 < - (a + a)" by (subst less_minus_iff, simp)
  moreover have "\<dots> \<longleftrightarrow> a < 0" by simp
  ultimately show ?thesis by blast
qed

declare neg_inf_eq_sup [simp] neg_sup_eq_inf [simp]

lemma le_minus_self_iff: "a \<le> - a \<longleftrightarrow> a \<le> 0"
proof -
  from add_le_cancel_left [of "uminus a" "plus a a" zero]
  have "(a <= -a) = (a+a <= 0)" 
    by (simp add: add_assoc[symmetric])
  thus ?thesis by simp
qed

lemma minus_le_self_iff: "- a \<le> a \<longleftrightarrow> 0 \<le> a"
proof -
  from add_le_cancel_left [of "uminus a" zero "plus a a"]
  have "(-a <= a) = (0 <= a+a)" 
    by (simp add: add_assoc[symmetric])
  thus ?thesis by simp
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

lemmas add_sup_inf_distribs = add_inf_distrib_right add_inf_distrib_left add_sup_distrib_right add_sup_distrib_left


class lattice_ab_group_add_abs = lattice_ab_group_add + abs +
  assumes abs_lattice: "\<bar>a\<bar> = sup a (- a)"
begin

lemma abs_prts: "\<bar>a\<bar> = pprt a - nprt a"
proof -
  have "0 \<le> \<bar>a\<bar>"
  proof -
    have a: "a \<le> \<bar>a\<bar>" and b: "- a \<le> \<bar>a\<bar>" by (auto simp add: abs_lattice)
    show ?thesis by (rule add_mono [OF a b, simplified])
  qed
  then have "0 \<le> sup a (- a)" unfolding abs_lattice .
  then have "sup (sup a (- a)) 0 = sup a (- a)" by (rule sup_absorb1)
  then show ?thesis
    by (simp add: add_sup_inf_distribs sup_aci
      pprt_def nprt_def diff_minus abs_lattice)
qed

subclass ordered_ab_group_add_abs
proof
  have abs_ge_zero [simp]: "\<And>a. 0 \<le> \<bar>a\<bar>"
  proof -
    fix a b
    have a: "a \<le> \<bar>a\<bar>" and b: "- a \<le> \<bar>a\<bar>" by (auto simp add: abs_lattice)
    show "0 \<le> \<bar>a\<bar>" by (rule add_mono [OF a b, simplified])
  qed
  have abs_leI: "\<And>a b. a \<le> b \<Longrightarrow> - a \<le> b \<Longrightarrow> \<bar>a\<bar> \<le> b"
    by (simp add: abs_lattice le_supI)
  fix a b
  show "0 \<le> \<bar>a\<bar>" by simp
  show "a \<le> \<bar>a\<bar>"
    by (auto simp add: abs_lattice)
  show "\<bar>-a\<bar> = \<bar>a\<bar>"
    by (simp add: abs_lattice sup_commute)
  show "a \<le> b \<Longrightarrow> - a \<le> b \<Longrightarrow> \<bar>a\<bar> \<le> b" by (fact abs_leI)
  show "\<bar>a + b\<bar> \<le> \<bar>a\<bar> + \<bar>b\<bar>"
  proof -
    have g:"abs a + abs b = sup (a+b) (sup (-a-b) (sup (-a+b) (a + (-b))))" (is "_=sup ?m ?n")
      by (simp add: abs_lattice add_sup_inf_distribs sup_aci diff_minus)
    have a:"a+b <= sup ?m ?n" by (simp)
    have b:"-a-b <= ?n" by (simp) 
    have c:"?n <= sup ?m ?n" by (simp)
    from b c have d: "-a-b <= sup ?m ?n" by(rule order_trans)
    have e:"-a-b = -(a+b)" by (simp add: diff_minus)
    from a d e have "abs(a+b) <= sup ?m ?n" 
      by (drule_tac abs_leI, auto)
    with g[symmetric] show ?thesis by simp
  qed
qed

end

lemma sup_eq_if:
  fixes a :: "'a\<Colon>{lattice_ab_group_add, linorder}"
  shows "sup a (- a) = (if a < 0 then - a else a)"
proof -
  note add_le_cancel_right [of a a "- a", symmetric, simplified]
  moreover note add_le_cancel_right [of "-a" a a, symmetric, simplified]
  then show ?thesis by (auto simp: sup_max min_max.sup_absorb1 min_max.sup_absorb2)
qed

lemma abs_if_lattice:
  fixes a :: "'a\<Colon>{lattice_ab_group_add_abs, linorder}"
  shows "\<bar>a\<bar> = (if a < 0 then - a else a)"
by auto

lemma estimate_by_abs:
  "a + b <= (c::'a::lattice_ab_group_add_abs) \<Longrightarrow> a <= c + abs b" 
proof -
  assume "a+b <= c"
  then have "a <= c+(-b)" by (simp add: algebra_simps)
  have "(-b) <= abs b" by (rule abs_ge_minus_self)
  then have "c + (- b) \<le> c + \<bar>b\<bar>" by (rule add_left_mono)
  with `a \<le> c + (- b)` show ?thesis by (rule order_trans)
qed

class lattice_ring = ordered_ring + lattice_ab_group_add_abs
begin

subclass semilattice_inf_ab_group_add ..
subclass semilattice_sup_ab_group_add ..

end

lemma abs_le_mult: "abs (a * b) \<le> (abs a) * (abs (b::'a::lattice_ring))" 
proof -
  let ?x = "pprt a * pprt b - pprt a * nprt b - nprt a * pprt b + nprt a * nprt b"
  let ?y = "pprt a * pprt b + pprt a * nprt b + nprt a * pprt b + nprt a * nprt b"
  have a: "(abs a) * (abs b) = ?x"
    by (simp only: abs_prts[of a] abs_prts[of b] algebra_simps)
  {
    fix u v :: 'a
    have bh: "\<lbrakk>u = a; v = b\<rbrakk> \<Longrightarrow> 
              u * v = pprt a * pprt b + pprt a * nprt b + 
                      nprt a * pprt b + nprt a * nprt b"
      apply (subst prts[of u], subst prts[of v])
      apply (simp add: algebra_simps) 
      done
  }
  note b = this[OF refl[of a] refl[of b]]
  have xy: "- ?x <= ?y"
    apply (simp)
    apply (rule order_trans [OF add_nonpos_nonpos add_nonneg_nonneg])
    apply (simp_all add: mult_nonneg_nonneg mult_nonpos_nonpos)
    done
  have yx: "?y <= ?x"
    apply (simp add:diff_minus)
    apply (rule order_trans [OF add_nonpos_nonpos add_nonneg_nonneg])
    apply (simp_all add: mult_nonneg_nonpos mult_nonpos_nonneg)
    done
  have i1: "a*b <= abs a * abs b" by (simp only: a b yx)
  have i2: "- (abs a * abs b) <= a*b" by (simp only: a b xy)
  show ?thesis
    apply (rule abs_leI)
    apply (simp add: i1)
    apply (simp add: i2[simplified minus_le_iff])
    done
qed

instance lattice_ring \<subseteq> ordered_ring_abs
proof
  fix a b :: "'a\<Colon> lattice_ring"
  assume a: "(0 \<le> a \<or> a \<le> 0) \<and> (0 \<le> b \<or> b \<le> 0)"
  show "abs (a*b) = abs a * abs b"
  proof -
    have s: "(0 <= a*b) | (a*b <= 0)"
      apply (auto)    
      apply (rule_tac split_mult_pos_le)
      apply (rule_tac contrapos_np[of "a*b <= 0"])
      apply (simp)
      apply (rule_tac split_mult_neg_le)
      apply (insert a)
      apply (blast)
      done
    have mulprts: "a * b = (pprt a + nprt a) * (pprt b + nprt b)"
      by (simp add: prts[symmetric])
    show ?thesis
    proof cases
      assume "0 <= a * b"
      then show ?thesis
        apply (simp_all add: mulprts abs_prts)
        apply (insert a)
        apply (auto simp add: 
          algebra_simps 
          iffD1[OF zero_le_iff_zero_nprt] iffD1[OF le_zero_iff_zero_pprt]
          iffD1[OF le_zero_iff_pprt_id] iffD1[OF zero_le_iff_nprt_id])
          apply(drule (1) mult_nonneg_nonpos[of a b], simp)
          apply(drule (1) mult_nonneg_nonpos2[of b a], simp)
        done
    next
      assume "~(0 <= a*b)"
      with s have "a*b <= 0" by simp
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
  assumes
  "a1 <= (a::'a::lattice_ring)"
  "a <= a2"
  "b1 <= b"
  "b <= b2"
  shows
  "a * b <= pprt a2 * pprt b2 + pprt a1 * nprt b2 + nprt a2 * pprt b1 + nprt a1 * nprt b1"
proof - 
  have "a * b = (pprt a + nprt a) * (pprt b + nprt b)" 
    apply (subst prts[symmetric])+
    apply simp
    done
  then have "a * b = pprt a * pprt b + pprt a * nprt b + nprt a * pprt b + nprt a * nprt b"
    by (simp add: algebra_simps)
  moreover have "pprt a * pprt b <= pprt a2 * pprt b2"
    by (simp_all add: assms mult_mono)
  moreover have "pprt a * nprt b <= pprt a1 * nprt b2"
  proof -
    have "pprt a * nprt b <= pprt a * nprt b2"
      by (simp add: mult_left_mono assms)
    moreover have "pprt a * nprt b2 <= pprt a1 * nprt b2"
      by (simp add: mult_right_mono_neg assms)
    ultimately show ?thesis
      by simp
  qed
  moreover have "nprt a * pprt b <= nprt a2 * pprt b1"
  proof - 
    have "nprt a * pprt b <= nprt a2 * pprt b"
      by (simp add: mult_right_mono assms)
    moreover have "nprt a2 * pprt b <= nprt a2 * pprt b1"
      by (simp add: mult_left_mono_neg assms)
    ultimately show ?thesis
      by simp
  qed
  moreover have "nprt a * nprt b <= nprt a1 * nprt b1"
  proof -
    have "nprt a * nprt b <= nprt a * nprt b1"
      by (simp add: mult_left_mono_neg assms)
    moreover have "nprt a * nprt b1 <= nprt a1 * nprt b1"
      by (simp add: mult_right_mono_neg assms)
    ultimately show ?thesis
      by simp
  qed
  ultimately show ?thesis
    by - (rule add_mono | simp)+
qed

lemma mult_ge_prts:
  assumes
  "a1 <= (a::'a::lattice_ring)"
  "a <= a2"
  "b1 <= b"
  "b <= b2"
  shows
  "a * b >= nprt a1 * pprt b2 + nprt a2 * nprt b2 + pprt a1 * pprt b1 + pprt a2 * nprt b1"
proof - 
  from assms have a1:"- a2 <= -a" by auto
  from assms have a2: "-a <= -a1" by auto
  from mult_le_prts[of "-a2" "-a" "-a1" "b1" b "b2", OF a1 a2 assms(3) assms(4), simplified nprt_neg pprt_neg] 
  have le: "- (a * b) <= - nprt a1 * pprt b2 + - nprt a2 * nprt b2 + - pprt a1 * pprt b1 + - pprt a2 * nprt b1" by simp  
  then have "-(- nprt a1 * pprt b2 + - nprt a2 * nprt b2 + - pprt a1 * pprt b1 + - pprt a2 * nprt b1) <= a * b"
    by (simp only: minus_le_iff)
  then show ?thesis by simp
qed

instance int :: lattice_ring
proof  
  fix k :: int
  show "abs k = sup k (- k)"
    by (auto simp add: sup_int_def)
qed

instance real :: lattice_ring
proof
  fix a :: real
  show "abs a = sup a (- a)"
    by (auto simp add: sup_real_def)
qed

end
