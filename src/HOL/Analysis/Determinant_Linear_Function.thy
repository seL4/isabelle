theory Determinant_Linear_Function

imports Determinants

begin

subsection \<open>Determinants of linear functions between Euclidean spaces\<close>

text \<open>
  \<^const>\<open>Determinants.det\<close> is the determinant of a square matrix. In the following, we define
  the equivalent notion of the determinant of an endomorphism (in a finite-dimensional vector
  space).
\<close>

abbreviation matrix_det :: "(('a :: comm_ring_1, 'b :: finite) vec, 'b) vec \<Rightarrow> 'a"
  where "matrix_det \<equiv> Determinants.det"

lemmas matrix_det_def = Determinants.det_def


context finite_dimensional_vector_space
begin

definition det :: "('b \<Rightarrow> 'b) \<Rightarrow> 'a" where
  "det f = (\<Sum>p | p permutes Basis. of_int (sign p) *
             (\<Prod>b\<in>Basis. representation Basis (f (p b)) b))"

lemma det_cong:
  assumes "\<And>b. b \<in> Basis \<Longrightarrow> f b = g b"
  shows   "local.det f = local.det g"
  unfolding local.det_def
  by (intro sum.cong arg_cong2[of _ _ _ _ "(*)"] refl prod.cong)
     (simp_all add: permutes_in_image assms)

lemma det_id [simp]: "local.det id = 1"
proof -
  have "local.det id =
          (\<Sum>p | p permutes Basis. of_int (sign p) * (\<Prod>b\<in>Basis. representation Basis (p b) b))"
    by (simp add: det_def)
  also have "(\<Sum>p | p permutes Basis. of_int (sign p) * (\<Prod>b\<in>Basis. representation Basis (p b) b)) =
             (\<Sum>p | p permutes Basis. of_int (sign p) * (if p = id then 1 else 0))"
    using finite_Basis representation_basis[OF independent_Basis]
  proof (intro sum.cong, goal_cases)
    case (2 p)
    show ?case
    proof (cases "p = id")
      case False
      then obtain b where "p b \<noteq> b"
        by (auto simp: fun_eq_iff)
      with 2 have "b \<in> Basis"
        using permutes_not_in[of p Basis b] by auto
      with \<open>p b \<noteq> b\<close> show ?thesis using finite_Basis 2
        by (auto simp: representation_basis[OF independent_Basis] permutes_in_image)
    qed (auto simp: representation_basis[OF independent_Basis])
  qed auto
  also have "\<dots> = (\<Sum>p \<in> {id :: 'b \<Rightarrow> 'b}. 1)"
    by (rule sum.mono_neutral_cong_right) (auto simp: finite_permutations finite_Basis)
  finally show ?thesis
    by simp
qed

lemma det_ident [simp]: "local.det (\<lambda>x. x) = 1"
  using det_id unfolding id_def by simp

lemma det_scale:
  "local.det (\<lambda>x. scale c (f x)) = c ^ dimension * local.det f"
proof -
  define r where "r = representation Basis"
  interpret r: Vector_Spaces.linear scale "(*)" "\<lambda>x. r x b" for b
    unfolding r_def by (intro linear_representation independent_Basis span_Basis)
  have "local.det (\<lambda>x. scale c (f x)) = 
          (\<Sum>p | p permutes Basis. of_int (sign p) * (\<Prod>b\<in>Basis. r (c *s f (p b)) b))"
    unfolding local.det_def r_def by simp
  also have "\<dots> = c ^ card Basis * (\<Sum>p | p permutes Basis. of_int (sign p) * (\<Prod>b\<in>Basis. r (f (p b)) b))"
    by (simp add: r.scale sum_distrib_left sum_distrib_right mult_ac prod.distrib)
  also have "\<dots> = c ^ dimension * local.det f"
    by (simp add: local.det_def r_def dimension_def)
  finally show ?thesis .
qed

lemma det_scale': "local.det (scale c) = c ^ dimension"
  by (simp add: det_scale)

lemma det_minus: "local.det (\<lambda>x. -f x) = (-1) ^ dimension * local.det f"
  using det_scale[of "-1" f] by simp

lemma det_minus': "local.det (\<lambda>x. -x) = (-1) ^ dimension"
  using det_scale[of "-1" id] by simp

text \<open>
  The determinant commutes with function composition.
\<close>
theorem det_compose:
  assumes f: "Vector_Spaces.linear scale scale f" and g: "Vector_Spaces.linear scale scale g"
  shows "local.det (f \<circ> g) = local.det f * local.det g"
proof -
  define r where "r = representation Basis"
  interpret f: Vector_Spaces.linear scale scale f
    by fact
  interpret g: Vector_Spaces.linear scale scale g
    by fact
  interpret r: Vector_Spaces.linear scale "(*)" "\<lambda>x. r x b" for b
    unfolding r_def by (intro linear_representation independent_Basis span_Basis)
  define s :: "('b \<Rightarrow> 'b) \<Rightarrow> 'a" where "s = of_int \<circ> sign"
  define P where "P = {p. p permutes Basis}"
  define P' where "P' = (Basis \<rightarrow>\<^sub>E Basis) \<inter> {f. inj_on f Basis}"
  define P_bad where "P_bad = (Basis \<rightarrow>\<^sub>E Basis) - {f. inj_on f Basis}"
  define R where "R = (\<lambda>p. (\<Sum>q\<in>P_bad. \<Prod>b\<in>Basis. r (f (q b)) b * r (g (p b)) (q b)))"

  have r: "(\<Sum>b\<in>Basis. r v b *s b) = v" for v unfolding r_def 
    by (rule sum_representation_eq) (use finite_Basis span_Basis independent_Basis in auto)
  have [simp]: "q b \<in> Basis \<longleftrightarrow> b \<in> Basis" if "q \<in> P" for q b
    using that by (simp add: permutes_in_image P_def)
  have [simp]: "inv p \<in> P" if "p \<in> P" for p
    using that unfolding P_def by (auto simp: permutes_inv)
  have [simp]: "p \<circ> q \<in> P" if "p \<in> P" "q \<in> P" for p q
    using that unfolding P_def by (auto simp: permutes_compose)
  have [simp]: "p (inv p x) = x" "inv p (p x) = x" "p \<circ> inv p = id" "inv p \<circ> p = id"
    if "p \<in> P" for p x
  proof -
    interpret p: bijection p
      by unfold_locales (use that in \<open>auto simp: P_def permutes_bij\<close>)
    show "p (inv p x) = x" "inv p (p x) = x" "p \<circ> inv p = id" "inv p \<circ> p = id"
      by simp_all
  qed
  have [simp]: "s (p \<circ> q) = s p * s q" if "p \<in> P" "q \<in> P" for p q
    unfolding s_def o_apply[of of_int] using that
    by (subst sign_compose) (auto simp: P_def sign_compose intro: permutes_imp_permutation finite_Basis)
  have [simp]: "f \<circ> p \<in> P_bad \<longleftrightarrow> f \<in> P_bad" if "p \<in> P" for f p
  proof -
    have "f \<circ> p \<in> P_bad" if "f \<in> P_bad" "p \<in> P" for f p
    proof -
      have p: "p permutes Basis"
        using that by (auto simp: P_def)
      from that have "\<not>inj_on f Basis"
        unfolding P_bad_def by blast
      hence "inj_on (f \<circ> p) Basis \<longleftrightarrow> inj_on f Basis"
        using comp_inj_on_iff[OF permutes_inj_on[OF p], of f Basis] permutes_image[OF p] by simp
      thus "f \<circ> p \<in> P_bad"
        using that by (auto simp: P_bad_def PiE_def extensional_def Pi_def permutes_in_image[OF p])
    qed
    from this[of f p] this[of "f \<circ> p" "inv p"] show ?thesis
      using that by (auto simp flip: o_assoc)
  qed

  have "local.det (f \<circ> g) = (\<Sum>p\<in>P. s p * (\<Prod>b\<in>Basis. r (f (g (p b))) b))"
    unfolding det_def r_def s_def P_def by simp
  also have "\<dots> = (\<Sum>p\<in>P. s p * (\<Sum>q\<in>P. (\<Prod>b\<in>Basis. r (f (q b)) b) * (\<Prod>b\<in>Basis. r (g (p (inv q b))) b)) + s p * R p)"
  proof (intro sum.cong refl, goal_cases)
    case p: (1 p)
    define restr :: "('b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'b" where "restr = (\<lambda>p. restrict p Basis)"
    define unrestr :: "('b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'b" where "unrestr = (\<lambda>p x. if x \<in> Basis then p x else x)"

    have "(\<Prod>b\<in>Basis. r (f (g (p b))) b) = (\<Prod>b\<in>Basis. r (f (\<Sum>b'\<in>Basis. r (g (p b)) b' *s b')) b)"
      by (subst r) auto
    also have "\<dots> = (\<Prod>b\<in>Basis. \<Sum>b'\<in>Basis. r (f b') b * r (g (p b)) b')"
      by (simp add: f.sum r.sum f.scale r.scale mult_ac)
    also have "\<dots> = (\<Sum>q\<in>Basis \<rightarrow>\<^sub>E Basis. \<Prod>b\<in>Basis. r (f (q b)) b * r (g (p b)) (q b))"
      by (subst prod_sum_PiE) (auto simp: finite_Basis)
    also have "Basis \<rightarrow>\<^sub>E Basis = P' \<union> P_bad"
      unfolding P'_def P_bad_def by blast
    have "(\<Sum>q\<in>Basis \<rightarrow>\<^sub>E Basis. \<Prod>b\<in>Basis. r (f (q b)) b * r (g (p b)) (q b)) =
               (\<Sum>q\<in>P'. \<Prod>b\<in>Basis. r (f (q b)) b * r (g (p b)) (q b)) + R p"
      unfolding \<open>Basis \<rightarrow>\<^sub>E Basis = P' \<union> P_bad\<close>
      by (subst sum.union_disjoint) (auto simp: P'_def P_bad_def R_def intro: finite_PiE finite_Basis)
    also have "(\<Sum>q\<in>P'. \<Prod>b\<in>Basis. r (f (q b)) b * r (g (p b)) (q b)) = 
               (\<Sum>q\<in>P. \<Prod>b\<in>Basis. r (f (q b)) b * r (g (p b)) (q b))"
    proof (rule sum.reindex_bij_witness[of _ restr unrestr], goal_cases)
      case (2 q)
      hence "inj_on q Basis" "q \<in> Basis \<rightarrow> Basis"
        by (auto simp: P'_def)
      hence "q ` Basis = Basis"
        by (meson Pi_mem endo_inj_surj image_subset_iff finite_Basis)
      with \<open>inj_on q Basis\<close> have "bij_betw q Basis Basis"
        unfolding bij_betw_def by blast
      hence "bij_betw (unrestr q) (Basis \<union> -Basis) (Basis \<union> -Basis)"
        unfolding unrestr_def by (rule bij_betw_disjoint_Un) (auto simp: bij_betw_def)
      hence "bij (unrestr q)"
        by simp
      moreover have "unrestr q x = x" if "x \<notin> Basis" for x
        using that by (auto simp: unrestr_def)
      ultimately have "unrestr q permutes Basis"
        unfolding permutes_def bij_iff by blast
      thus ?case
        by (auto simp: P_def unrestr_def)
    qed (auto simp: unrestr_def restr_def fun_eq_iff P_def permutes_not_in P'_def permutes_inj_on)
    also have "\<dots> = (\<Sum>q\<in>P. (\<Prod>b\<in>Basis. r (f (q b)) b) * (\<Prod>b\<in>Basis. r (g (p b)) (q b)))"
      by (simp add: prod.distrib)
    also have "\<dots> = (\<Sum>q\<in>P. (\<Prod>b\<in>Basis. r (f (q b)) b) * (\<Prod>b\<in>Basis. r (g (p (inv q b))) b))"
    proof (intro sum.cong refl arg_cong2[of _ _ _ _ "(*)"], goal_cases)
      case q: (1 q)
      interpret bijection q
        by unfold_locales (use q permutes_bij[of q] in \<open>auto simp: P_def\<close>)
      show "(\<Prod>b\<in>Basis. r (g (p b)) (q b)) = (\<Prod>b\<in>Basis. r (g (p (inv q b))) b)"
        by (rule prod.reindex_bij_witness[of _ "inv q" q]) (use q in simp_all)
    qed
    finally show ?case
      by (simp add: algebra_simps)
  qed
  also have "\<dots> = (\<Sum>p\<in>P. \<Sum>q\<in>P. s p * (\<Prod>b\<in>Basis. r (f (q b)) b) * (\<Prod>b\<in>Basis. r (g (p (inv q b))) b)) + 
                  (\<Sum>p\<in>P. s p * R p)"
    by (simp add: sum_distrib_left mult.assoc sum.distrib)
  also have "(\<Sum>p\<in>P. \<Sum>q\<in>P. s p * (\<Prod>b\<in>Basis. r (f (q b)) b) * (\<Prod>b\<in>Basis. r (g (p (inv q b))) b)) =
             (\<Sum>(p,q)\<in>P\<times>P. s p * (\<Prod>b\<in>Basis. r (f (q b)) b) * (\<Prod>b\<in>Basis. r (g (p (inv q b))) b))"
    by (subst sum.cartesian_product) auto
  also have "\<dots> = (\<Sum>(p,q)\<in>P\<times>P. s (p \<circ> q) * (\<Prod>b\<in>Basis. r (f (q b)) b) * (\<Prod>b\<in>Basis. r (g (p b)) b))"
    by (rule sum.reindex_bij_witness[of _ "\<lambda>(p,q). (p \<circ> q, q)" "\<lambda>(p,q). (p \<circ> inv q, q)"])
       (auto simp: fun_eq_iff simp flip: o_assoc)
  also have "\<dots> = (\<Sum>q\<in>P. s q * (\<Prod>b\<in>Basis. r (f (q b)) b)) * (\<Sum>p\<in>P. s p * (\<Prod>b\<in>Basis. r (g (p b)) b))"
    unfolding sum_distrib_left unfolding sum_distrib_right
    by (simp add: algebra_simps flip: sum.cartesian_product)
  also have "\<dots> = local.det f * local.det g"
    by (simp add: det_def P_def s_def r_def)
  also have "(\<Sum>p\<in>P. s p * R p) = 0"
  proof -
    define R' where "R' = (\<lambda>p q. \<Prod>b\<in>Basis. r (f (q b)) b * r (g (p b)) (q b))"
    have "(\<Sum>p\<in>P. s p * R p) = (\<Sum>p\<in>P. \<Sum>q\<in>P_bad. s p * (\<Prod>b\<in>Basis. r (f (q b)) b * r (g (p b)) (q b)))"
      by (simp add: R_def sum_distrib_left)
    also have "\<dots> = (\<Sum>p\<in>P. \<Sum>q\<in>P_bad. s p * (\<Prod>b\<in>Basis. r (f ((q \<circ> p) b)) b * r (g (p b)) ((q \<circ> p) b)))"
    proof (rule sum.cong[OF refl], goal_cases)
      case (1 p)
      show ?case
        by (rule sum.reindex_bij_witness[of _ "\<lambda>q. q \<circ> p" "\<lambda>q. q \<circ> inv p"]) (use 1 in auto)
    qed
    also have "\<dots> = (\<Sum>q\<in>P_bad. \<Sum>p\<in>P. s p * (\<Prod>b\<in>Basis. r (f (q (p b))) b * r (g (p b)) (q (p b))))"
      by (subst sum.swap) (simp_all add: mult_ac)
    also have "\<dots> = (\<Sum>q\<in>P_bad. 0)"
    proof (intro sum.cong refl, goal_cases)
      case (1 q)
      from 1 obtain b1 b2 where b12: "b1 \<in> Basis" "b2 \<in> Basis" "b1 \<noteq> b2" "q b1 = q b2"
        unfolding P_bad_def inj_on_def by blast
      define t where "t = Transposition.transpose b1 b2"
      have [simp]: "t \<circ> t = id" "s t = -1"
        using b12 by (auto simp: t_def s_def sign_swap_id)
      have [simp]: "t \<in> P"
        using b12 by (auto simp: P_def t_def permutes_swap_id)
      have s: "s (t \<circ> p) = -s p" if "p \<in> P" for p
        using that by simp

      define h where "h = (\<lambda>p. ((\<Prod>b\<in>Basis. r (f (q (p b))) b) * (\<Prod>b\<in>Basis. r (g b) (q b))))"

      have "(\<Sum>p\<in>P. s p * (\<Prod>b\<in>Basis. r (f (q (p b))) b * r (g (p b)) (q (p b)))) = (\<Sum>p\<in>P. s p * h p)"
        unfolding prod.distrib h_def
      proof (intro sum.cong arg_cong2[of _ _ _ _ "(*)"] refl, goal_cases)
        case (1 p)
        show "(\<Prod>b\<in>Basis. r (g (p b)) (q (p b))) = (\<Prod>b\<in>Basis. r (g b) (q b))"
          by (rule prod.reindex_bij_witness[of _ "inv p" p]) (use 1 in simp_all)
      qed
      also have "(\<Sum>p\<in>P. s p * h p) = 0"
      proof (rule sum_involution_eq_0)
        fix p assume p: "p \<in> P"
        have "permutation p"
          using P_def finite_Basis p permutes_imp_permutation by auto
        hence "evenperm (t \<circ> p) \<longleftrightarrow> \<not>evenperm p"
          using b12 by (subst evenperm_comp) (auto simp: t_def evenperm_swap permutation_swap_id)
        thus "t \<circ> p \<noteq> p"
          by metis
        have "s (t \<circ> p) = -s p"
          using p by auto
        moreover have "h (t \<circ> p) = h p" unfolding h_def using b12
          by (intro arg_cong2[of _ _ _ _ "(*)"] refl prod.cong)
             (auto simp: h_def t_def Transposition.transpose_def)
        ultimately show "s (t \<circ> p) * h (t \<circ> p) + s p * h p = 0"
          by simp
      qed (auto simp: o_assoc)
      finally show ?case .
    qed
    finally show ?thesis
      by simp
  qed
  finally show ?thesis
    by (simp add: o_def)
qed

lemma det_permute:
  assumes "q permutes Basis"
  shows   "local.det (f \<circ> q) = of_int (sign q) * local.det f"
proof -
  have "local.det (f \<circ> q) = (\<Sum>p | p permutes Basis. 
           of_int (sign p) * (\<Prod>b\<in>Basis. representation Basis (f ((q \<circ> p) b)) b))"
    unfolding det_def by (simp add: o_def)
  also have "\<dots> = (\<Sum>p | p permutes Basis. of_int (sign q) * (of_int (sign (q \<circ> p)) * 
                     (\<Prod>b\<in>Basis. representation Basis (f ((q \<circ> p) b)) b)))"
    by (intro sum.cong refl, subst sign_compose)
       (use assms in \<open>auto simp flip: of_int_mult intro: permutes_imp_permutation finite_Basis\<close>)
  also have "\<dots> = (\<Sum>p | p permutes Basis. of_int (sign q) * (of_int (sign p) *
                    (\<Prod>b\<in>Basis. representation Basis (f (p b)) b)))"
    by (rule sum.reindex_bij_witness[of _ "\<lambda>p. inv q \<circ> p" "\<lambda>p. q \<circ> p"])
       (use assms in \<open>simp_all add: permutes_compose permutes_inv permutes_inv_o o_assoc\<close>)
  also have "\<dots> = of_int (sign q) * local.det f"
    by (simp only: det_def sum_distrib_left)
  finally show ?thesis .
qed

lemma det_permute':
  assumes "q permutes Basis"
  shows   "local.det q = of_int (sign q)"
  using det_permute[OF assms, of id] by simp

lemma det_bij_betw_Basis:
  assumes "bij_betw q Basis Basis"
  shows   "local.det q = of_int (sign_on Basis q)"
proof -
  have "local.det q = local.det (restrict_id q Basis)"
    by (rule det_cong) auto
  also have "\<dots> = of_int (sign_on Basis q)"
    by (subst det_permute') (auto simp: sign_on_def intro!: permutes_restrict_id assms)
  finally show ?thesis .
qed

corollary det_inv:
  assumes "Vector_Spaces.linear scale scale f" "inj f"
  shows   "local.det (inv f) = inverse (local.det f)"
proof -
  have "bij f"
    using assms by (simp add: bijI linear_inj_imp_surj)
  interpret f: bijection f
    by standard fact
  have "local.det (f \<circ> inv f) = 1"
    by simp
  also have "local.det (f \<circ> inv f) = local.det f * local.det (inv f)"
    using assms \<open>inj f\<close> by (subst det_compose) (auto simp: inj_linear_imp_inv_linear)
  finally show ?thesis
    by (auto simp: divide_simps mult_ac)
qed

lemma inj_imp_det_nonzero:
  assumes "Vector_Spaces.linear scale scale f"  "inj f"
  shows   "local.det f \<noteq> 0"
proof
  assume [simp]: "local.det f = 0"
  hence "bij f"
    using assms by (simp add: bijI linear_inj_imp_surj)
  interpret f: bijection f
    by standard fact
  have "local.det (f \<circ> inv f) = 1"
    by simp
  also have "local.det (f \<circ> inv f) = 0"
    using assms \<open>inj f\<close> by (subst local.det_compose) (auto simp: inj_linear_imp_inv_linear)
  finally show False
    by simp
qed

text \<open>
  The determinant vanishes if and only if the function is not a bijection.
\<close>
theorem det_eq_0_iff:
  assumes "Vector_Spaces.linear scale scale f"
  shows   "local.det f = 0 \<longleftrightarrow> \<not>inj f"
proof (cases "Basis = {}")
  case True
  hence "(\<forall>x::'b. x = 0)" using span_Basis
    by auto
  hence "inj f"
    unfolding inj_def by metis
  moreover have "local.det f = 1"
    unfolding det_def by (subst (2 3) True) auto
  ultimately show ?thesis
    by simp
next
  case False
  then obtain b where b: "b \<in> Basis"
    by blast

  have "local.det f = 0" if "\<not>inj f"
  proof -
    from \<open>\<not>inj f\<close> obtain x where x: "x \<noteq> 0" "f x = 0"
      by (meson assms module_hom.inj_iff_eq_0 module_hom_eq_linear)
    from b have "independent {b}"
      by auto
    then obtain g where g: "Vector_Spaces.linear scale scale g" "inj g" "g b = x"
      using linear_independent_extend_inj[of "{b}" "\<lambda>_. x"] x by auto
    interpret g: bijection g
      by unfold_locales (use g in \<open>simp add: bijI linear_inj_imp_surj\<close>)
    have "local.det f = local.det (inv g \<circ> f \<circ> g)"
      using assms g
      by (auto simp: Vector_Spaces.linear_compose inj_linear_imp_inv_linear
                     det_compose det_inv inj_imp_det_nonzero)
    also have "\<dots> = (\<Sum>p | p permutes Basis. 0)"
      unfolding det_def
    proof (rule sum.cong, goal_cases)
      case (2 p)
      interpret p: bijection p
        using 2 by (simp add: bijection_def permutes_bij)
      interpret invg: Vector_Spaces.linear scale scale "inv g"
        using g(1,2) by (intro inj_linear_imp_inv_linear)
      have "inv p b \<in> Basis"
        using b 2 permutes_in_image by fastforce
      hence "(\<exists>a\<in>Basis. representation Basis (inv g (f (g (p a)))) a = 0)"
        by (intro bexI[of _ "inv p b"]) (auto simp: g(3) x representation_zero)
      thus ?case
        using finite_Basis by simp
    qed auto
    finally show "local.det f = 0"
      by simp
  qed
  thus ?thesis
    using inj_imp_det_nonzero[OF assms] by auto
qed

end


text \<open>
  The determinant is invariant under basis changes:
\<close>
theorem (in finite_dimensional_vector_space_pair) det_basis_change:
  assumes "Vector_Spaces.linear (*a) (*b) h" "bij_betw h B1 B2"
  shows   "vs1.det f = vs2.det (h \<circ> f \<circ> inv h)"
proof -
  define r1 where "r1 = vs1.representation B1"
  define r2 where "r2 = vs2.representation B2"
  interpret r1: Vector_Spaces.linear "(*a)" "(*)" "\<lambda>x. r1 x b" for b
    unfolding r1_def
    by (rule vs1.linear_representation) (auto simp: vs1.independent_Basis vs1.span_Basis)
  interpret r2: Vector_Spaces.linear "(*b)" "(*)" "\<lambda>x. r2 x b" for b
    unfolding r2_def
    by (rule vs2.linear_representation) (auto simp: vs2.independent_Basis vs2.span_Basis)

  have "bij h"
    by (metis assms bijI bij_betw_finite bij_betw_iff_card bij_betw_imp_surj_on
              local.linear_span_image local.linear_surjective_imp_injective vs1.dim_UNIV
              vs1.finite_Basis vs1.span_Basis vs2.dim_UNIV vs2.span_Basis)
  note h = this assms(2)
  interpret h: Vector_Spaces.linear "(*a)" "(*b)" h
    by fact
  interpret inv_h: Vector_Spaces.linear "(*b)" "(*a)" "inv h"
    by (meson h(1) h.module_hom_axioms local.bij_module_hom_imp_inv_module_hom module_hom_eq_linear)

  have bij_betw_inv_h: "bij_betw (inv h) B2 B1"
    using h by (metis bij_betw_def inj_imp_bij_betw_inv)
  have [simp]: "h x = h y \<longleftrightarrow> x = y" for x y
    using h(1) by (auto simp: bij_def inj_def)
  have [simp]: "inv h \<circ> h = id"
    by (simp add: bij_is_inj h(1))
  hence [simp]: "inv h (h x) = x" for x
    unfolding fun_eq_iff o_def id_def by blast
  have [simp]: "h \<circ> inv h = id"
    by (meson bij_betw_def h(1) surj_iff)
  hence [simp]: "h (inv h x) = x" for x
    unfolding fun_eq_iff o_def id_def by blast
  define map1 where "map1 = map_permutation B1 h"
  define map2 where "map2 = map_permutation B2 (inv h)"

  have r1_conv_r2: "r1 x b = r2 (h x) (h b)" for x b
  proof -
    have *: "r1 b' b = r2 (h b') (h b)" if "b' \<in> B1" for b'
    proof -
      have *: "h b' \<in> B2"
        using h(2) that by (auto simp: bij_betw_def)
      show ?thesis
      unfolding r1_def r2_def
        by (subst vs1.representation_basis[OF vs1.independent_Basis that(1)],
            subst vs2.representation_basis[OF vs2.independent_Basis *(1)]) auto
    qed
    obtain c where x: "x = (\<Sum>v\<in>B1. c v *a v)"
      using vs1.span_Basis unfolding vs1.span_finite[OF vs1.finite_Basis] by blast
    show ?thesis
      by (simp add: x r1.sum r2.sum r1.scale r2.scale h.sum h.scale *)
  qed

  have "vs1.det f = (\<Sum>p | p permutes B1. of_int (sign p) * (\<Prod>b\<in>B1. r1 (f (p b)) b))"
    unfolding vs1.det_def r1_def ..
  also have "\<dots> = (\<Sum>p | p permutes B2. of_int (sign p) * (\<Prod>b\<in>B1. r1 (f (map2 p b)) b))"
    using h bij_betw_imp_inj_on[OF bij_betw_inv_h] vs1.finite_Basis bij_betw_imp_inj_on[OF h(2)]
    by (intro sum.reindex_bij_witness[of _ map2 map1])
       (auto simp: map1_def map2_def sign_map_permutation 
                   map_permutation_compose[OF h(2)]
                   map_permutation_compose[OF bij_betw_inv_h] bij_is_inj
             intro!: map_permutation_permutes bij_betw_inv_h h)
  also have "\<dots> = (\<Sum>p | p permutes B2. of_int (sign p) * (\<Prod>b\<in>B2. r2 ((h \<circ> f \<circ> inv h) (p b)) b))"
  proof (intro sum.cong arg_cong2[of _ _ _ _ "(*)"] refl, goal_cases)
    case p: (1 p)
    have "(\<Prod>b\<in>B1. r1 (f (map2 p b)) b) = (\<Prod>b\<in>B2. r1 (f (inv h (p b))) (inv h b))"
      using bij_betw_inv_h p 
      by (intro prod.reindex_bij_witness[of _ "inv h" h])
         (auto simp: bij_betw_def map2_def map_permutation_apply[OF bij_betw_imp_inj_on[OF bij_betw_inv_h]])
    also have "\<dots> = (\<Prod>b\<in>B2. r2 ((h \<circ> f \<circ> inv h) (p b)) b)"
      by (intro prod.cong refl) (auto simp: r1_conv_r2)
    finally show ?case .
  qed
  also have "\<dots> = vs2.det (h \<circ> f \<circ> inv h)"
    unfolding vs2.det_def r2_def ..
  finally show ?thesis .
qed

text \<open>
  To compute the determinant of a linear function, we can choose whichever basis is
  most convenient for us.
\<close>
corollary (in finite_dimensional_vector_space) det_eq:
  assumes f: "Vector_Spaces.linear scale scale f" and B: "independent B" "span B = UNIV"
  shows   "local.det f =
             (\<Sum>p | p permutes B. of_int (sign p) * (\<Prod>b\<in>B. representation B (f (p b)) b))"
proof -
  have [simp, intro]: "finite B"
    by (rule finiteI_independent) fact
  interpret B: finite_dimensional_vector_space scale B
    by standard (use B in auto)
  interpret pair: finite_dimensional_vector_space_pair scale Basis scale B ..

  have "local.dimension = B.dimension"
    using B B.dim_UNIV local.dim_UNIV unfolding local.dimension_def B.dimension_def by simp
  then obtain h where h: "Vector_Spaces.linear scale scale h" "bij h" "bij_betw h Basis B"
    using pair.basis_change_exists by blast
  have h_inv: "Vector_Spaces.linear scale scale (inv h)"
    by (rule inj_linear_imp_inv_linear) (use h in \<open>auto simp: bij_is_inj\<close>)

  have "local.det f = B.det (h \<circ> f \<circ> inv h)"
    by (rule pair.det_basis_change) fact+
  also have "\<dots> = B.det f"
    using h h_inv bij_is_inj[of h] B.det_eq_0_iff[of h]
    by (simp add: f h B.det_compose B.det_inv Vector_Spaces.linear_compose[of _ scale] field_simps)
  finally show ?thesis
    by (simp add: B.det_def)
qed


text \<open>
  In particular, this gives us a notion of determinant for linear maps in a Euclidean space
  (in the sence of the \<^class>\<open>euclidean_space\<close> type class).
\<close>
lemma eucl_det_def:
  "eucl.det f = (\<Sum>p | p permutes Basis. of_int (sign p) * (\<Prod>b\<in>Basis. f (p b) \<bullet> b))"
  by (simp add: eucl.det_def representation_euclidean_space)

text \<open>
  The determinant of an endomorphism of $\mathbb{R}^n$ is equal to the determinant
  of the matrix representing it.
\<close>
lemma eucl_det_conv_matrix_det:
  fixes f :: "real ^ 'n \<Rightarrow> real ^ 'n"
  assumes "linear f"
  shows   "eucl.det f = matrix_det (matrix f)"
proof -
  define g where "g = (\<lambda>i. axis i 1 :: real ^ 'n)"
  define g' where "g' = inv g"
  define h where "h = map_permutation UNIV g"
  define h' where "h' = map_permutation Basis g'"
  have "inj g"
    unfolding g_def by (auto intro!: injI simp: axis_eq_axis)
  hence [simp]: "g' (g i) = i" for i
    by (simp add: inj_iff g'_def)
  have [simp]: "g (g' b) = b" if "b \<in> Basis" for b
    using that inv_f_f[of g] \<open>inj g\<close> by (auto simp: Basis_vec_def g_def g'_def)
  have bij_g: "bij_betw g UNIV Basis"
    using \<open>inj g\<close> unfolding bij_betw_def Basis_vec_def by (auto simp: g_def)
  have [intro]: "h p permutes Basis" if "p permutes UNIV" for p
    unfolding h_def by (intro map_permutation_permutes that bij_g)
  have [intro]: "h' p permutes UNIV" if "p permutes Basis" for p
    unfolding h'_def g'_def
    by (intro map_permutation_permutes that bij_g bij_betw_inv_into)
  have [simp]: "h' (h p) = p" if "p permutes UNIV" for p
    unfolding h'_def h_def g'_def
    by (subst map_permutation_compose_inv) (use bij_g that in \<open>auto simp flip: g'_def\<close>)
  have [simp]: "h (h' p) = p" if "p permutes Basis" for p
    unfolding h'_def h_def g'_def using bij_betw_inv_into[OF bij_g]
    by (subst map_permutation_compose_inv) (use bij_g that in \<open>auto simp flip: g'_def\<close>)
  have [simp]: "g b \<in> Basis" for b
    unfolding Basis_vec_def g_def by auto

  have "matrix_det (matrix f) = (\<Sum>p | p permutes UNIV. of_int (sign p) * (\<Prod>i\<in>UNIV. matrix f $ i $ p i))"
    unfolding matrix_det_def ..
  also have "\<dots> = (\<Sum>p | p permutes Basis. of_int (sign p) * (\<Prod>b\<in>Basis. f (p b) \<bullet> b))"
  proof (intro sum.reindex_bij_witness[of _ h' h] arg_cong2[of _ _ _ _ "(*)"] 
               arg_cong[of _ _ of_int] prod.reindex_bij_witness[of _ g g'])
    fix p :: "'n \<Rightarrow> 'n" and b :: "real ^ 'n"
    assume p: "p \<in> {p. p permutes UNIV}" and b: "b \<in> Basis"
    from b obtain i where [simp]: "b = axis i 1"
      unfolding Basis_vec_def by auto
    have "matrix f $ g' b $ p (g' b) = f (g (p (g' (g i)))) $ g' (g i)"
      unfolding matrix_def g_def by (auto simp: h_def)
    also have "\<dots> = f (g (p i)) $ i"
      by simp
    also have "\<dots> = f (map_permutation UNIV g p (g i)) $ i"
      by (subst map_permutation_apply) (use \<open>inj g\<close> in auto)
    also have "\<dots> = f (h p b) \<bullet> b"
      by (simp add: h_def g_def inner_axis)
    finally show "matrix f $ g' b $ p (g' b) = f (h p b) \<bullet> b" .
  next
    fix p :: "'n \<Rightarrow> 'n"
    assume p: "p \<in> {p. p permutes UNIV}"
    thus "sign (h p) = sign p"
      unfolding h_def using \<open>inj g\<close> by (subst sign_map_permutation) auto
  qed auto
  also have "\<dots> = eucl.det f"
    unfolding eucl_det_def ..
  finally show ?thesis ..
qed


subsection \<open>Absolute determinant of a multiset\<close>

text \<open>
  For the ``normal'' determinant of a list of vectors, the order of the vectors matters insofar
  as it determines the sign. If we look at the absolute value of the determinant, however, the
  order does not matter and we can therefore define the absolute determinant of a (finite) multiset
  of vectors.

  This can e.g.\ be useful to check whether a multiset of vectors is dependent or not.
\<close>
definition abs_det :: "('a :: euclidean_space) multiset \<Rightarrow> real" where
  "abs_det X = (if size X \<noteq> DIM('a) then 0 
                else (THE d. \<forall>f. image_mset f (mset_set Basis) = X \<longrightarrow> \<bar>eucl.det f\<bar> = d))"

lemma abs_det_eq_0 [simp]:
  "size (X :: 'a multiset) \<noteq> DIM('a :: euclidean_space) \<Longrightarrow> abs_det X = 0"
  by (simp add: abs_det_def)

lemma abs_det_conv_det:
  assumes "image_mset f (mset_set (Basis :: 'a :: euclidean_space set)) = (X :: 'a multiset)"
  shows   "abs_det X = \<bar>eucl.det f\<bar>"
proof -
  have size_eq: "size X = DIM('a)"
    by (subst assms [symmetric]) auto
  hence abs_det_eq:
    "abs_det X = (THE d. \<forall>f'. image_mset f' (mset_set Basis) = 
                   image_mset f (mset_set Basis) \<longrightarrow> \<bar>eucl.det f'\<bar> = d)"
    by (simp add: abs_det_def flip: assms)
  fix X :: "'a multiset"
  have "\<bar>eucl.det f\<bar> = \<bar>eucl.det g\<bar>"
    if eq: "image_mset f (mset_set Basis) = image_mset g (mset_set Basis)" for f g :: "'a \<Rightarrow> 'a"
  proof -
    obtain p where p: "p permutes Basis" "\<And>x. x \<in> Basis \<Longrightarrow> f x = g (p x)"
      using image_mset_eq_implies_permutes[OF finite_Basis eq] by metis
    have "eucl.det f = eucl.det (g \<circ> p)"
      by (rule eucl.det_cong) (auto simp: p)
    also have "\<dots> = sign p * eucl.det g"
      by (rule eucl.det_permute) fact
    finally show "\<bar>eucl.det f\<bar> = \<bar>eucl.det g\<bar>"
      by (simp add: abs_mult sign_def flip: of_int_abs)
  qed
  hence "\<exists>!d. \<forall>g::'a \<Rightarrow> 'a. image_mset g (mset_set Basis) =
           image_mset f (mset_set Basis) \<longrightarrow> \<bar>eucl.det g\<bar> = d"
    by blast
  from theI'[OF this, folded abs_det_eq] show ?thesis
    by simp
qed

lemma abs_det: "abs_det (image_mset f (mset_set Basis)) = \<bar>eucl.det f\<bar>"
  by (rule abs_det_conv_det) auto

lemma abs_det_empty [simp]: "abs_det {#} = 0"
  by simp

lemma representation_real: "representation {1} x = (\<lambda>b. if b = 1 then x else 0)"
  using representation_euclidean_space[of x] by (auto split: if_splits)

lemma det_real [simp]: "eucl.det (f :: real \<Rightarrow> real) = f 1"
  unfolding eucl.det_def representation_euclidean_space by (auto simp: sign_id)

lemma det_real' [simp]: "finite_dimensional_vector_space.det scaleR {1} f = f 1"
  using det_real[of f] by (simp del: det_real)

lemma det_complex: "eucl.det f = Re (f 1) * Im (f \<i>) - Re (f \<i>) * Im (f 1)"
proof -
  have [simp]: "id \<noteq> Transposition.transpose 1 \<i>"
    by (auto simp: Transposition.transpose_def fun_eq_iff)
  have "eucl.det (f :: complex \<Rightarrow> complex) =
          (\<Sum>p | p permutes {1, \<i>}. real_of_int (sign p) * (Re (f (p 1)) * Im (f (p \<i>))))"
    unfolding eucl.det_def representation_euclidean_space
    by (simp add: representation_euclidean_space Basis_complex_def )
  also have "{p. p permutes {1, \<i>}} = {id, Transposition.transpose 1 \<i>}"
    by (auto simp: permutes_doubleton_iff)
  also have "(\<Sum>p\<in>\<dots>. real_of_int (sign p) * (Re (f (p 1)) * Im (f (p \<i>)))) =
               Re (f 1) * Im (f \<i>) - Re (f \<i>) * Im (f 1)"
    by (subst sum.insert) (auto simp: sign_id sign_swap_id fun_eq_iff intro!: exI[of _ 1])
  finally show ?thesis .
qed

lemma det_pair_real:
  "eucl.det f = fst (f (1, 0)) * snd (f (0, 1)) - fst (f (0, 1)) * snd (f (1, 0))" (is "_ = ?rhs") 
proof -
  have *: "{p. p permutes Basis} = {id, Transposition.transpose (0,1) (1::real,0::real)}"
    by (auto simp: permutes_doubleton_iff Basis_pair_def)
  have neq: "id \<noteq> Transposition.transpose (0, 1) (1::real, 0::real)"
    by (auto simp: fun_eq_iff Transposition.transpose_def)
  show ?thesis
    unfolding eucl_det_def * neq
    by (simp add: Basis_pair_def permutes_doubleton_iff neq sign_id sign_swap_id inner_prod_def)
qed

lemma abs_det_real:
  "abs_det {# x::real #} = \<bar>x\<bar>"
  using abs_det_conv_det[of "\<lambda>_. x" "{#x#}"] unfolding det_real by simp

lemma abs_det_complex:
  "abs_det {# u, v :: complex #} = \<bar>Re u * Im v - Re v * Im u\<bar>"
proof (subst abs_det_conv_det[of "\<lambda>b. if b = 1 then u else v"])
  show "{#if b = 1 then u else v. b \<in># mset_set (Basis :: complex set)#} = {# u, v #}"
    by (auto simp: Basis_complex_def)
qed (auto simp: det_complex)

end