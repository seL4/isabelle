header {*Borel Sets*}

theory Borel
  imports Measure
begin

text{*From the Hurd/Coble measure theory development, translated by Lawrence Paulson.*}

definition borel_space where
  "borel_space = sigma (UNIV::real set) (range (\<lambda>a::real. {x. x \<le> a}))"

definition borel_measurable where
  "borel_measurable a = measurable a borel_space"

definition indicator_fn where
  "indicator_fn s = (\<lambda>x. if x \<in> s then 1 else (0::real))"

definition mono_convergent where
  "mono_convergent u f s \<equiv>
        (\<forall>x m n. m \<le> n \<and> x \<in> s \<longrightarrow> u m x \<le> u n x) \<and>
        (\<forall>x \<in> s. (\<lambda>i. u i x) ----> f x)"

lemma in_borel_measurable:
   "f \<in> borel_measurable M \<longleftrightarrow>
    sigma_algebra M \<and>
    (\<forall>s \<in> sets (sigma UNIV (range (\<lambda>a::real. {x. x \<le> a}))).
      f -` s \<inter> space M \<in> sets M)"
apply (auto simp add: borel_measurable_def measurable_def borel_space_def) 
apply (metis PowD UNIV_I Un_commute sigma_algebra_sigma subset_Pow_Union subset_UNIV subset_Un_eq) 
done

lemma (in sigma_algebra) borel_measurable_const:
   "(\<lambda>x. c) \<in> borel_measurable M"
  by (auto simp add: in_borel_measurable prems)

lemma (in sigma_algebra) borel_measurable_indicator:
  assumes a: "a \<in> sets M"
  shows "indicator_fn a \<in> borel_measurable M"
apply (auto simp add: in_borel_measurable indicator_fn_def prems)
apply (metis Diff_eq Int_commute a compl_sets) 
done

lemma Collect_eq: "{w \<in> X. f w \<le> a} = {w. f w \<le> a} \<inter> X"
  by (metis Collect_conj_eq Collect_mem_eq Int_commute)

lemma (in measure_space) borel_measurable_le_iff:
   "f \<in> borel_measurable M = (\<forall>a. {w \<in> space M. f w \<le> a} \<in> sets M)"
proof 
  assume f: "f \<in> borel_measurable M"
  { fix a
    have "{w \<in> space M. f w \<le> a} \<in> sets M" using f
      apply (auto simp add: in_borel_measurable sigma_def Collect_eq)
      apply (drule_tac x="{x. x \<le> a}" in bspec, auto)
      apply (metis equalityE rangeI subsetD sigma_sets.Basic)  
      done
    }
  thus "\<forall>a. {w \<in> space M. f w \<le> a} \<in> sets M" by blast
next
  assume "\<forall>a. {w \<in> space M. f w \<le> a} \<in> sets M"
  thus "f \<in> borel_measurable M" 
    apply (simp add: borel_measurable_def borel_space_def Collect_eq) 
    apply (rule measurable_sigma, auto) 
    done
qed

lemma Collect_less_le:
     "{w \<in> X. f w < g w} = (\<Union>n. {w \<in> X. f w \<le> g w - inverse(real(Suc n))})"
  proof auto
    fix w
    assume w: "f w < g w"
    hence nz: "g w - f w \<noteq> 0"
      by arith
    with w have "real(Suc(natceiling(inverse(g w - f w)))) > inverse(g w - f w)"
      by (metis lessI order_le_less_trans real_natceiling_ge real_of_nat_less_iff)       hence "inverse(real(Suc(natceiling(inverse(g w - f w)))))
             < inverse(inverse(g w - f w))" 
      by (metis less_iff_diff_less_0 less_imp_inverse_less linorder_neqE_ordered_idom nz positive_imp_inverse_positive real_le_anti_sym real_less_def w)
    hence "inverse(real(Suc(natceiling(inverse(g w - f w))))) < g w - f w"
      by (metis inverse_inverse_eq order_less_le_trans real_le_refl) 
    thus "\<exists>n. f w \<le> g w - inverse(real(Suc n))" using w
      by (rule_tac x="natceiling(inverse(g w - f w))" in exI, auto)
  next
    fix w n
    assume le: "f w \<le> g w - inverse(real(Suc n))"
    hence "0 < inverse(real(Suc n))"
      by (metis inverse_real_of_nat_gt_zero)
    thus "f w < g w" using le
      by arith 
  qed


lemma (in sigma_algebra) sigma_le_less:
  assumes M: "!!a::real. {w \<in> space M. f w \<le> a} \<in> sets M"
  shows "{w \<in> space M. f w < a} \<in> sets M"
proof -
  show ?thesis using Collect_less_le [of "space M" f "\<lambda>x. a"]
    by (auto simp add: countable_UN M) 
qed

lemma (in sigma_algebra) sigma_less_ge:
  assumes M: "!!a::real. {w \<in> space M. f w < a} \<in> sets M"
  shows "{w \<in> space M. a \<le> f w} \<in> sets M"
proof -
  have "{w \<in> space M. a \<le> f w} = space M - {w \<in> space M. f w < a}"
    by auto
  thus ?thesis using M
    by auto
qed

lemma (in sigma_algebra) sigma_ge_gr:
  assumes M: "!!a::real. {w \<in> space M. a \<le> f w} \<in> sets M"
  shows "{w \<in> space M. a < f w} \<in> sets M"
proof -
  show ?thesis using Collect_less_le [of "space M" "\<lambda>x. a" f]
    by (auto simp add: countable_UN le_diff_eq M) 
qed

lemma (in sigma_algebra) sigma_gr_le:
  assumes M: "!!a::real. {w \<in> space M. a < f w} \<in> sets M"
  shows "{w \<in> space M. f w \<le> a} \<in> sets M"
proof -
  have "{w \<in> space M. f w \<le> a} = space M - {w \<in> space M. a < f w}" 
    by auto
  thus ?thesis
    by (simp add: M compl_sets)
qed

lemma (in measure_space) borel_measurable_gr_iff:
   "f \<in> borel_measurable M = (\<forall>a. {w \<in> space M. a < f w} \<in> sets M)"
proof (auto simp add: borel_measurable_le_iff sigma_gr_le) 
  fix u
  assume M: "\<forall>a. {w \<in> space M. f w \<le> a} \<in> sets M"
  have "{w \<in> space M. u < f w} = space M - {w \<in> space M. f w \<le> u}"
    by auto
  thus "{w \<in> space M. u < f w} \<in> sets M"
    by (force simp add: compl_sets countable_UN M)
qed

lemma (in measure_space) borel_measurable_less_iff:
   "f \<in> borel_measurable M = (\<forall>a. {w \<in> space M. f w < a} \<in> sets M)"
proof (auto simp add: borel_measurable_le_iff sigma_le_less) 
  fix u
  assume M: "\<forall>a. {w \<in> space M. f w < a} \<in> sets M"
  have "{w \<in> space M. f w \<le> u} = space M - {w \<in> space M. u < f w}"
    by auto
  thus "{w \<in> space M. f w \<le> u} \<in> sets M"
    using Collect_less_le [of "space M" "\<lambda>x. u" f] 
    by (force simp add: compl_sets countable_UN le_diff_eq sigma_less_ge M)
qed

lemma (in measure_space) borel_measurable_ge_iff:
   "f \<in> borel_measurable M = (\<forall>a. {w \<in> space M. a \<le> f w} \<in> sets M)"
proof (auto simp add: borel_measurable_less_iff sigma_le_less sigma_ge_gr sigma_gr_le) 
  fix u
  assume M: "\<forall>a. {w \<in> space M. f w < a} \<in> sets M"
  have "{w \<in> space M. u \<le> f w} = space M - {w \<in> space M. f w < u}"
    by auto
  thus "{w \<in> space M. u \<le> f w} \<in> sets M"
    by (force simp add: compl_sets countable_UN M)
qed

lemma (in measure_space) affine_borel_measurable:
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. a + (g x) * b) \<in> borel_measurable M"
proof (cases rule: linorder_cases [of b 0])
  case equal thus ?thesis
    by (simp add: borel_measurable_const)
next
  case less
    {
      fix w c
      have "a + g w * b \<le> c \<longleftrightarrow> g w * b \<le> c - a"
        by auto
      also have "... \<longleftrightarrow> (c-a)/b \<le> g w" using less
        by (metis divide_le_eq less less_asym)
      finally have "a + g w * b \<le> c \<longleftrightarrow> (c-a)/b \<le> g w" .
    }
    hence "\<And>w c. a + g w * b \<le> c \<longleftrightarrow> (c-a)/b \<le> g w" .
    thus ?thesis using less g
      by (simp add: borel_measurable_ge_iff [of g]) 
         (simp add: borel_measurable_le_iff)
next
  case greater
    hence 0: "\<And>x c. (g x * b \<le> c - a) \<longleftrightarrow> (g x \<le> (c - a) / b)"
      by (metis mult_imp_le_div_pos le_divide_eq) 
    have 1: "\<And>x c. (a + g x * b \<le> c) \<longleftrightarrow> (g x * b \<le> c - a)"
      by auto
    from greater g
    show ?thesis
      by (simp add: borel_measurable_le_iff 0 1) 
qed

definition
  nat_to_rat_surj :: "nat \<Rightarrow> rat" where
 "nat_to_rat_surj n = (let (i,j) = nat_to_nat2 n
                       in Fract (nat_to_int_bij i) (nat_to_int_bij j))"

lemma nat_to_rat_surj: "surj nat_to_rat_surj"
proof (auto simp add: surj_def nat_to_rat_surj_def) 
  fix y
  show "\<exists>x. y = (\<lambda>(i, j). Fract (nat_to_int_bij i) (nat_to_int_bij j)) (nat_to_nat2 x)"
  proof (cases y)
    case (Fract a b)
      obtain i where i: "nat_to_int_bij i = a" using surj_nat_to_int_bij
        by (metis surj_def) 
      obtain j where j: "nat_to_int_bij j = b" using surj_nat_to_int_bij
        by (metis surj_def)
      obtain n where n: "nat_to_nat2 n = (i,j)" using nat_to_nat2_surj
        by (metis surj_def)

      from Fract i j n show ?thesis
        by (metis prod.cases prod_case_split)
  qed
qed

lemma rats_enumeration: "\<rat> = range (of_rat o nat_to_rat_surj)" 
  using nat_to_rat_surj
  by (auto simp add: image_def surj_def) (metis Rats_cases) 

lemma (in measure_space) borel_measurable_less_borel_measurable:
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "{w \<in> space M. f w < g w} \<in> sets M"
proof -
  have "{w \<in> space M. f w < g w} =
        (\<Union>r\<in>\<rat>. {w \<in> space M. f w < r} \<inter> {w \<in> space M. r < g w })"
    by (auto simp add: Rats_dense_in_real)
  thus ?thesis using f g 
    by (simp add: borel_measurable_less_iff [of f]  
                  borel_measurable_gr_iff [of g]) 
       (blast intro: gen_countable_UN [OF rats_enumeration])
qed
 
lemma (in measure_space) borel_measurable_leq_borel_measurable:
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "{w \<in> space M. f w \<le> g w} \<in> sets M"
proof -
  have "{w \<in> space M. f w \<le> g w} = space M - {w \<in> space M. g w < f w}" 
    by auto 
  thus ?thesis using f g 
    by (simp add: borel_measurable_less_borel_measurable compl_sets)
qed

lemma (in measure_space) borel_measurable_eq_borel_measurable:
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "{w \<in> space M. f w = g w} \<in> sets M"
proof -
  have "{w \<in> space M. f w = g w} =
        {w \<in> space M. f w \<le> g w} \<inter> {w \<in> space M. g w \<le> f w}"
    by auto
  thus ?thesis using f g 
    by (simp add: borel_measurable_leq_borel_measurable Int) 
qed

lemma (in measure_space) borel_measurable_neq_borel_measurable:
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "{w \<in> space M. f w \<noteq> g w} \<in> sets M"
proof -
  have "{w \<in> space M. f w \<noteq> g w} = space M - {w \<in> space M. f w = g w}"
    by auto
  thus ?thesis using f g 
    by (simp add: borel_measurable_eq_borel_measurable compl_sets) 
qed

lemma (in measure_space) borel_measurable_add_borel_measurable:
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x + g x) \<in> borel_measurable M"
proof -
  have 1:"!!a. {w \<in> space M. a \<le> f w + g w} = {w \<in> space M. a + (g w) * -1 \<le> f w}"
    by auto
  have "!!a. (\<lambda>w. a + (g w) * -1) \<in> borel_measurable M"
    by (rule affine_borel_measurable [OF g]) 
  hence "!!a. {w \<in> space M. (\<lambda>w. a + (g w) * -1)(w) \<le> f w} \<in> sets M" using f
    by (rule borel_measurable_leq_borel_measurable) 
  hence "!!a. {w \<in> space M. a \<le> f w + g w} \<in> sets M"
    by (simp add: 1) 
  thus ?thesis
    by (simp add: borel_measurable_ge_iff) 
qed


lemma (in measure_space) borel_measurable_square:
  assumes f: "f \<in> borel_measurable M"
  shows "(\<lambda>x. (f x)^2) \<in> borel_measurable M"
proof -
  {
    fix a
    have "{w \<in> space M. (f w)\<twosuperior> \<le> a} \<in> sets M"
    proof (cases rule: linorder_cases [of a 0])
      case less
      hence "{w \<in> space M. (f w)\<twosuperior> \<le> a} = {}" 
        by auto (metis less order_le_less_trans power2_less_0)
      also have "... \<in> sets M"
        by (rule empty_sets) 
      finally show ?thesis .
    next
      case equal
      hence "{w \<in> space M. (f w)\<twosuperior> \<le> a} = 
             {w \<in> space M. f w \<le> 0} \<inter> {w \<in> space M. 0 \<le> f w}"
        by auto
      also have "... \<in> sets M"
        apply (insert f) 
        apply (rule Int) 
        apply (simp add: borel_measurable_le_iff)
        apply (simp add: borel_measurable_ge_iff)
        done
      finally show ?thesis .
    next
      case greater
      have "\<forall>x. (f x ^ 2 \<le> sqrt a ^ 2) = (- sqrt a  \<le> f x & f x \<le> sqrt a)"
        by (metis abs_le_interval_iff abs_of_pos greater real_sqrt_abs
                  real_sqrt_le_iff real_sqrt_power)
      hence "{w \<in> space M. (f w)\<twosuperior> \<le> a} =
             {w \<in> space M. -(sqrt a) \<le> f w} \<inter> {w \<in> space M. f w \<le> sqrt a}" 
        using greater by auto
      also have "... \<in> sets M"
        apply (insert f) 
        apply (rule Int) 
        apply (simp add: borel_measurable_ge_iff)
        apply (simp add: borel_measurable_le_iff)
        done
      finally show ?thesis .
    qed
  }
  thus ?thesis by (auto simp add: borel_measurable_le_iff) 
qed

lemma times_eq_sum_squares:
   fixes x::real
   shows"x*y = ((x+y)^2)/4 - ((x-y)^ 2)/4"
by (simp add: power2_eq_square ring_distribs diff_divide_distrib [symmetric]) 


lemma (in measure_space) borel_measurable_uminus_borel_measurable:
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. - g x) \<in> borel_measurable M"
proof -
  have "(\<lambda>x. - g x) = (\<lambda>x. 0 + (g x) * -1)"
    by simp
  also have "... \<in> borel_measurable M" 
    by (fast intro: affine_borel_measurable g) 
  finally show ?thesis .
qed

lemma (in measure_space) borel_measurable_times_borel_measurable:
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x * g x) \<in> borel_measurable M"
proof -
  have 1: "(\<lambda>x. 0 + (f x + g x)\<twosuperior> * inverse 4) \<in> borel_measurable M"
    by (fast intro: affine_borel_measurable borel_measurable_square 
                    borel_measurable_add_borel_measurable f g) 
  have "(\<lambda>x. -((f x + -g x) ^ 2 * inverse 4)) = 
        (\<lambda>x. 0 + ((f x + -g x) ^ 2 * inverse -4))"
    by (simp add: Ring_and_Field.minus_divide_right) 
  also have "... \<in> borel_measurable M" 
    by (fast intro: affine_borel_measurable borel_measurable_square 
                    borel_measurable_add_borel_measurable 
                    borel_measurable_uminus_borel_measurable f g)
  finally have 2: "(\<lambda>x. -((f x + -g x) ^ 2 * inverse 4)) \<in> borel_measurable M" .
  show ?thesis
    apply (simp add: times_eq_sum_squares real_diff_def) 
    using 1 2 apply (simp add: borel_measurable_add_borel_measurable) 
    done
qed

lemma (in measure_space) borel_measurable_diff_borel_measurable:
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x - g x) \<in> borel_measurable M"
unfolding real_diff_def
  by (fast intro: borel_measurable_add_borel_measurable 
                  borel_measurable_uminus_borel_measurable f g)

lemma (in measure_space) mono_convergent_borel_measurable:
  assumes u: "!!n. u n \<in> borel_measurable M"
  assumes mc: "mono_convergent u f (space M)"
  shows "f \<in> borel_measurable M"
proof -
  {
    fix a
    have 1: "!!w. w \<in> space M & f w <= a \<longleftrightarrow> w \<in> space M & (\<forall>i. u i w <= a)"
      proof safe
        fix w i
        assume w: "w \<in> space M" and f: "f w \<le> a"
        hence "u i w \<le> f w"
          by (auto intro: SEQ.incseq_le
                   simp add: incseq_def mc [unfolded mono_convergent_def])
        thus "u i w \<le> a" using f
          by auto
      next
        fix w 
        assume w: "w \<in> space M" and u: "\<forall>i. u i w \<le> a"
        thus "f w \<le> a"
          by (metis LIMSEQ_le_const2 mc [unfolded mono_convergent_def])
      qed
    have "{w \<in> space M. f w \<le> a} = {w \<in> space M. (\<forall>i. u i w <= a)}"
      by (simp add: 1)
    also have "... = (\<Inter>i. {w \<in> space M. u i w \<le> a})" 
      by auto
    also have "...  \<in> sets M" using u
      by (auto simp add: borel_measurable_le_iff intro: countable_INT) 
    finally have "{w \<in> space M. f w \<le> a} \<in> sets M" .
  }
  thus ?thesis 
    by (auto simp add: borel_measurable_le_iff) 
qed

lemma (in measure_space) borel_measurable_setsum_borel_measurable:
  assumes s: "finite s"
  shows "(!!i. i \<in> s ==> f i \<in> borel_measurable M) \<Longrightarrow> (\<lambda>x. setsum (\<lambda>i. f i x) s) \<in> borel_measurable M" using s
proof (induct s)
  case empty
  thus ?case
    by (simp add: borel_measurable_const)
next
  case (insert x s)
  thus ?case
    by (auto simp add: borel_measurable_add_borel_measurable) 
qed

end
