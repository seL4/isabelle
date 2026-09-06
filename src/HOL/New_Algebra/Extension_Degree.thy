section \<open>Degree of a simple algebraic extension\<close>

theory Extension_Degree
  imports Simple_Extension Extension_Vector_Space
begin

text \<open>This theory begins the \<^emph>\<open>field side\<close> of phase R2.  For an element @{term a} algebraic over a
  subfield @{term K}, it turns the \<^emph>\<open>predicate\<close> @{const is_minpoly} into a genuine \<^emph>\<open>function\<close>
  @{term "minpoly K a"} (the minimal polynomial is unique) and defines the degree of the simple
  extension @{term "K(a)"} over @{term K} as @{term "degree (minpoly K a)"}.\<close>

subsection \<open>Uniqueness of the minimal polynomial\<close>

context Subfield
begin

text \<open>The minimal polynomial is unique: two minimal polynomials of @{term a} over @{term K} divide
  each other (each is a @{term K}-annihilator of @{term a}, so a multiple of the other by
  @{thm [source] minpoly_dvd}), and being monic they must be equal.\<close>
lemma minpoly_unique:
  assumes m1: "is_minpoly K a m1" and m2: "is_minpoly K a m2"
  shows "m1 = m2"
proof -
  have k1: "m1 \<in> poly_over K" "lead_coeff m1 = 1" "poly m1 a = 0"
    using m1 by (auto simp: is_minpoly_def)
  have k2: "m2 \<in> poly_over K" "lead_coeff m2 = 1" "poly m2 a = 0"
    using m2 by (auto simp: is_minpoly_def)
  have d12: "m1 dvd m2" using minpoly_dvd[OF m1 k2(1) k2(3)] .
  have d21: "m2 dvd m1" using minpoly_dvd[OF m2 k1(1) k1(3)] .
  from d12 obtain u where u: "m2 = m1 * u" ..
  from d21 obtain v where v: "m1 = m2 * v" ..
  have m1nz: "m1 \<noteq> 0" using k1(2) by auto
  have "m1 = m2 * v" by (rule v)
  also have "\<dots> = m1 * (u * v)" using u by (simp add: mult.assoc)
  finally have uv: "u * v = 1" using m1nz by simp
  have unz: "u \<noteq> 0" using uv by auto
  obtain c where uc: "u = [:c:]" 
    by (metis dvd_triv_left is_unit_poly_iff uv)
  have "lead_coeff m2 = lead_coeff m1 * lead_coeff u" using u by (simp add: lead_coeff_mult)
  then have "c = 1" using k1(2) k2(2) uc by simp
  then show ?thesis using u uc by simp
qed

end (* subfield *)

subsection \<open>The minimal polynomial as a function\<close>

text \<open>The minimal polynomial of @{term a} over @{term K}.  For @{term a} algebraic over @{term K}
  this is the unique monic polynomial of least degree over @{term K} vanishing at @{term a};
  otherwise it is an unspecified default.\<close>
definition minpoly :: "'a :: field set \<Rightarrow> 'a \<Rightarrow> 'a poly"
  where "minpoly K a = (SOME m. is_minpoly K a m)"

text \<open>The degree of the simple extension @{term "K(a)"} over @{term K}.\<close>
definition ext_degree :: "'a :: field set \<Rightarrow> 'a \<Rightarrow> nat"
  where "ext_degree K a = degree (minpoly K a)"

context Subfield
begin

text \<open>For an algebraic element, @{const minpoly} genuinely is a minimal polynomial.\<close>
lemma is_minpoly_minpoly:
  assumes "algebraic_over K a"
  shows "is_minpoly K a (minpoly K a)"
  unfolding minpoly_def by (rule someI_ex[OF minpoly_exists[OF assms]])

text \<open>\ldots and it is \<^emph>\<open>the\<close> minimal polynomial: any minimal polynomial equals it.\<close>
lemma minpoly_eq:
  assumes "algebraic_over K a" and "is_minpoly K a m"
  shows "minpoly K a = m"
  using minpoly_unique[OF is_minpoly_minpoly[OF assms(1)] assms(2)] .

lemma minpoly_over: "algebraic_over K a \<Longrightarrow> minpoly K a \<in> poly_over K"
  using is_minpoly_minpoly by (simp add: is_minpoly_def)

lemma minpoly_monic: "algebraic_over K a \<Longrightarrow> lead_coeff (minpoly K a) = 1"
  using is_minpoly_minpoly by (simp add: is_minpoly_def)

lemma minpoly_root: "algebraic_over K a \<Longrightarrow> poly (minpoly K a) a = 0"
  using is_minpoly_minpoly by (simp add: is_minpoly_def)

lemma minpoly_nonzero:
  assumes "algebraic_over K a" shows "minpoly K a \<noteq> 0"
  using assms minpoly_monic by fastforce

subsection \<open>The extension degree\<close>

text \<open>The degree of a simple algebraic extension is positive.\<close>
lemma ext_degree_pos:
  assumes "algebraic_over K a"
  shows "ext_degree K a > 0"
  unfolding ext_degree_def using minpoly_degree_pos[OF is_minpoly_minpoly[OF assms]] .

text \<open>For an element already in @{term K}, its minimal polynomial is the linear @{term "[:-a, 1:]"}.\<close>
lemma is_minpoly_linear:
  assumes a: "a \<in> K"
  shows "is_minpoly K a [:-a, 1:]"
  unfolding is_minpoly_def
proof (intro conjI ballI impI)
  show "[:- a, 1:] \<in> poly_over K"
    using a by (auto intro!: poly_over_pCons poly_over_1 uminus_closed)
  show "lead_coeff [:- a, 1:] = 1" by simp
  show "poly [:- a, 1:] a = 0" by simp
  fix r assume r: "r \<in> poly_over K" and rnz: "r \<noteq> 0 \<and> poly r a = 0"
  show "degree [:- a, 1:] \<le> degree r"
    by (meson divides_degree poly_eq_0_iff_dvd rnz)
qed

text \<open>Consequently an element of @{term K} is algebraic and has extension degree @{term 1}.\<close>
lemma algebraic_over_self:
  assumes "a \<in> K"
  shows "algebraic_over K a"
  using is_minpoly_linear[OF assms]
  by (auto simp: algebraic_over_def is_minpoly_def intro!: bexI[of _ "[:-a, 1:]"])

lemma minpoly_in_field:
  assumes "a \<in> K"
  shows "minpoly K a = [:- a, 1:]"
  using minpoly_eq[OF algebraic_over_self[OF assms] is_minpoly_linear[OF assms]] .

lemma ext_degree_in_field:
  assumes "a \<in> K"
  shows "ext_degree K a = 1"
  unfolding ext_degree_def by (simp add: minpoly_in_field[OF assms])

text \<open>\<^emph>\<open>Degree one characterises membership.\<close>  An algebraic element has extension degree \<open>1\<close>
  exactly when it already lies in \<open>K\<close>: a monic degree-one minimal polynomial is \<open>[:c, 1:]\<close> with
  \<open>c \<in> K\<close>, and vanishing at \<open>a\<close> forces \<open>a = -c \<in> K\<close>.\<close>
lemma ext_degree_eq_1_iff:
  assumes "algebraic_over K a"
  shows "ext_degree K a = 1 \<longleftrightarrow> a \<in> K"
proof
  assume "ext_degree K a = 1"
  then have deg: "degree (minpoly K a) = 1" by (simp add: ext_degree_def)
  have monic: "lead_coeff (minpoly K a) = 1" using minpoly_monic[OF assms] .
  have root: "poly (minpoly K a) a = 0" using minpoly_root[OF assms] .
  \<comment> \<open>Expand the root condition coefficientwise: @{term "poly (minpoly K a) a"} is the sum over
    @{term "{..1}"}, i.e.\ @{term "coeff (minpoly K a) 0 + coeff (minpoly K a) 1 * a"}.\<close>
  have lc1: "coeff (minpoly K a) 1 = 1" using deg monic by simp
  have c0K: "coeff (minpoly K a) 0 \<in> K"
    by (simp add: assms minpoly_over poly_over_coeff)
  have "coeff (minpoly K a) 0 + a = 0" 
    using deg lc1 root by (simp add: poly_altdef)
  then show "a \<in> K"
    by (metis add_eq_0_iff c0K Subfield.uminus_closed Subfield_axioms)
next
  assume "a \<in> K"
  then show "ext_degree K a = 1" by (rule ext_degree_in_field)
qed

text \<open>@{const poly_over} is closed under finite sums (needed to build a polynomial from a
  coordinate function).\<close>
lemma poly_over_sum:
  assumes "\<And>i. i \<in> A \<Longrightarrow> f i \<in> poly_over K"
  shows "(\<Sum>i \<in> A. f i) \<in> poly_over K"
  using assms by (induction A rule: infinite_finite_induct) (auto intro: poly_over_add)

subsection \<open>The power basis of a simple algebraic extension\<close>

text \<open>\<^emph>\<open>Spanning.\<close>  Every element of the simple extension @{term "eval_img K a"} is a
  @{term K}-linear combination of the powers @{term "1 :: 'a"}, @{term a}, \ldots,
  @{term "a ^ (ext_degree K a - 1)"}.  Given @{term "y = poly p a"}, divide @{term p} by the
  (monic) minimal polynomial @{term "minpoly K a"}; the quotient term vanishes at @{term a}
  (as @{term "poly (minpoly K a) a = 0"}), leaving a remainder of degree @{text "< d"} whose
  coefficients supply the combination.\<close>
lemma power_basis_span:
  assumes alg: "algebraic_over K a" and y: "y \<in> eval_img K a"
  shows "\<exists>c. (\<forall>i < ext_degree K a. c i \<in> K) \<and> y = (\<Sum>i < ext_degree K a. c i * a ^ i)"
proof -
  define m where "m = minpoly K a"
  define d where "d = ext_degree K a"
  have mK: "m \<in> poly_over K" using minpoly_over[OF alg] by (simp add: m_def)
  have monic: "lead_coeff m = 1" using minpoly_monic[OF alg] by (simp add: m_def)
  have mdeg: "degree m = d" by (simp add: d_def ext_degree_def m_def)
  have ddeg: "degree m > 0" using ext_degree_pos[OF alg] mdeg by (simp add: d_def)
  have mroot: "poly m a = 0" using minpoly_root[OF alg] by (simp add: m_def)
  obtain p where p: "p \<in> poly_over K" and yp: "y = poly p a"
    using eval_imgE[OF y] by blast
  obtain q r where qr: "q \<in> poly_over K" "r \<in> poly_over K"
      "p = q * m + r" "degree r < degree m"
    using poly_over_divmod_exists[OF mK monic ddeg p] by blast
  have rdeg: "degree r < d" using qr(4) mdeg by simp
  have y_r: "y = poly r a"
    using yp qr(3) mroot by simp
  have "poly r a = (\<Sum>i \<le> degree r. coeff r i * a ^ i)" by (rule poly_altdef)
  also have "\<dots> = (\<Sum>i < d. coeff r i * a ^ i)"
    by (rule sum.mono_neutral_left) (use rdeg in \<open>auto simp: coeff_eq_0\<close>)
  finally have "y = (\<Sum>i < d. coeff r i * a ^ i)" using y_r by simp
  moreover have "\<forall>i < d. coeff r i \<in> K" using qr(2) by (auto simp: poly_over_coeff)
  ultimately show ?thesis unfolding d_def by blast
qed

text \<open>\<^emph>\<open>Independence.\<close>  The powers @{term "1 :: 'a"}, @{term a}, \ldots, @{term "a ^ (ext_degree K a - 1)"}
  are @{term K}-linearly independent: a vanishing combination has all coefficients @{term 0}.  The
  combination is @{term "poly r a"} for @{term "r = (\<Sum>i<d. monom (c i) i)"}, a polynomial over
  @{term K} of degree @{text "< d"}; were it nonzero it would annihilate @{term a} below the minimal
  degree, so @{term "r = 0"} and every coefficient @{term "c i"} vanishes.\<close>
lemma power_basis_indep:
  assumes alg: "algebraic_over K a"
    and cK: "\<And>i. i < ext_degree K a \<Longrightarrow> c i \<in> K"
    and zero: "(\<Sum>i < ext_degree K a. c i * a ^ i) = 0"
  shows "\<forall>i < ext_degree K a. c i = 0"
proof -
  define d where "d = ext_degree K a"
  have dpos: "d > 0" using ext_degree_pos[OF alg] by (simp add: d_def)
  define r where "r = (\<Sum>i < d. monom (c i) i)"
  \<comment> \<open>@{term r} lies over @{term K}, has degree below @{term d}, and annihilates @{term a}.\<close>
  have rK: "r \<in> poly_over K"
    unfolding r_def using cK
    by (auto intro!: poly_over_sum poly_over_monom simp: d_def)
  have "degree r \<le> d - 1"
    unfolding r_def
    by (rule degree_sum_le) (auto intro: order_trans[OF degree_monom_le])
  then have rdeg: "degree r < d"
    by (simp add: dpos order_le_less_trans)
  have coeff_r: "coeff r j = c j" if "j < d" for j
    using that by (simp add: coeff_sum r_def)
  have rroot: "poly r a = 0"
    using zero by(force simp add: poly_sum poly_monom r_def d_def)
  \<comment> \<open>Below the minimal degree a nonzero annihilator is impossible, so @{term "r = 0"}.\<close>
  have r0: "r = 0"
    using is_minpoly_minpoly[OF alg] rK rroot unfolding is_minpoly_def
    by (metis d_def ext_degree_def leD rdeg)
  show ?thesis
    using coeff_r d_def r0 by auto
qed

end (* subfield *)


context subfield_tower
begin

text \<open>For a simple algebraic extension, the vector-space dimension is the existing minimal-polynomial
  degree.  The proof turns the power-basis spanning and independence results into the coordinate-map
  basis used by @{const vs.dimension}; the explicit equality is the API bridge between the two
  presentations of extension degree.\<close>
theorem simple_extension_dimension_eq_ext_degree:
  assumes alg: "algebraic_over K a" and L_def: "L = eval_img K a"
  shows "vs.dimension = ext_degree K a"
proof -
  define d where "d = ext_degree K a"
  define B where "B = (\<lambda>i. a ^ i) ` {..<d}"
  have finB: "finite B" by (simp add: B_def)
  have aL: "a \<in> L"
    unfolding L_def by (rule Subfield.eval_img_self[OF base.Subfield_axioms])
  have powL: "a ^ i \<in> L" for i
    using aL by (rule ext.power_closed)
  have BL: "B \<subseteq> L" using powL by (auto simp: B_def)
  have spanL: "L \<subseteq> vs.span B"
  proof
    fix y assume yL: "y \<in> L"
    obtain c where cK: "\<And>i. i < d \<Longrightarrow> c i \<in> K"
        and yc: "y = (\<Sum>i < d. c i * a ^ i)"
      using Subfield.power_basis_span[OF base.Subfield_axioms alg]
        yL by (auto simp: L_def d_def)
    have sum_span:
        "(\<Sum>i < d. c i * a ^ i) \<in> vs.span ((\<lambda>i. a ^ i) ` {..<d})"
      by (rule sum_scale_in_span) (auto simp: cK powL)
    then show "y \<in> vs.span B" using yc by (simp add: B_def)
  qed
  have mod_span: "vs.mod.spanning B"
    by (rule vs.mod.spanningI[OF BL]) (use spanL in blast)
  have spanB: "vs.spanning B"
    by (rule iffD2[OF vs.spanning_iff_mod_spanning[OF finB BL] mod_span])
  have power_inj: "inj_on (\<lambda>i. a ^ i) {..<d}"
  proof (rule inj_onI)
    fix i j assume i: "i \<in> {..<d}" and j: "j \<in> {..<d}"
      and eq: "a ^ i = a ^ j"
    show "i = j"
    proof (rule ccontr)
      assume neq: "i \<noteq> j"
      define c where "c = (\<lambda>k. if k = i then (1 :: 'a) else if k = j then - 1 else 0)"
      have neg_one: "-(1 :: 'a) \<in> K"
        by (rule base.uminus_closed) (rule base.one_closed)
      have cK: "\<And>k. k < d \<Longrightarrow> c k \<in> K"
      proof -
        fix k assume kd: "k < d"
        have h1: "k = i \<or> k \<noteq> i" by blast
        then show "c k \<in> K"
        proof (elim disjE)
          assume h1: "k = i"
          have "c k = (1 :: 'a)"
            unfolding c_def using h1 by simp
          then show ?thesis using base.one_closed by simp
        next
          assume h1: "k \<noteq> i"
          have h2: "k = j \<or> k \<noteq> j" by blast
          then show ?thesis
          proof (elim disjE)
            assume h2: "k = j"
            have "c k = -(1 :: 'a)"
              unfolding c_def using h1 h2 by simp
            then show ?thesis using neg_one by simp
          next
            assume h2: "k \<noteq> j"
            have "c k = (0 :: 'a)"
              unfolding c_def using h1 h2 by simp
            then show ?thesis using base.zero_closed by simp
          qed
        qed
      qed
      have sum0: "(\<Sum>k < d. c k * a ^ k) = 0"
      proof -
        have point:
            "c k * a ^ k = (if k = i then a ^ k else if k = j then -(a ^ k) else 0)" for k
          unfolding c_def
          by (simp split: if_split)
        have sum_eq:
            "(\<Sum>k < d. c k * a ^ k) =
              (\<Sum>k < d. if k = i then a ^ k else if k = j then -(a ^ k) else 0)"
          by (simp add: point)
        also have "\<dots> = a ^ i - a ^ j"
          using i j neq by (simp add: sum.If_cases)
        also have "\<dots> = 0" using eq by simp
        finally show ?thesis .
      qed
      have cK': "\<And>k. k < ext_degree K a \<Longrightarrow> c k \<in> K"
        using cK by (simp add: d_def)
      have sum0': "(\<Sum>k < ext_degree K a. c k * a ^ k) = 0"
        using sum0 by (simp add: d_def)
      have all0: "\<forall>k < d. c k = 0"
        unfolding d_def
        by (rule Subfield.power_basis_indep[OF base.Subfield_axioms alg cK' sum0'])
      have ci0: "c i = 0" using all0 i by blast
      have ci1: "c i = (1 :: 'a)" unfolding c_def using neq by simp
      show False using ci0 ci1 by simp
    qed
  qed
  have indB: "vs.lin_indep B"
    unfolding vs.lin_indep_def
  proof (intro conjI)
    show "finite B" by (rule finB)
    show "B \<subseteq> L" by (rule BL)
    show "\<forall>c \<in> B \<rightarrow>\<^sub>E K. vs.lincomb c B = 0 \<longrightarrow>
      (\<forall>v \<in> B. c v = 0)"
    proof (rule ballI, rule impI)
      fix c assume cB: "c \<in> B \<rightarrow>\<^sub>E K" and zero: "vs.lincomb c B = 0"
      have cK: "\<And>v. v \<in> B \<Longrightarrow> c v \<in> K" using cB by auto
      have sum0: "(\<Sum>v \<in> B. c v * v) = 0"
        using vs_lincomb_eq_sum[OF finB BL cK] zero by simp
      have indexed: "(\<Sum>i < d. c (a ^ i) * a ^ i) = 0"
      proof -
        have reindexed:
            "(\<Sum>v \<in> B. c v * v) = (\<Sum>i < d. c (a ^ i) * a ^ i)"
          unfolding B_def
          by (subst sum.reindex[OF power_inj]) (simp add: o_def)
        then show ?thesis using sum0 by simp
      qed
      have cK': "\<And>i. i < ext_degree K a \<Longrightarrow> c (a ^ i) \<in> K"
        using cK by (auto simp: B_def d_def)
      have indexed': "(\<Sum>i < ext_degree K a. c (a ^ i) * a ^ i) = 0"
        using indexed by (simp add: d_def)
      have all0: "\<forall>i < d. c (a ^ i) = 0"
        unfolding d_def
        by (rule Subfield.power_basis_indep[OF base.Subfield_axioms alg cK' indexed'])
      show "\<forall>v \<in> B. c v = 0"
        using all0 by (auto simp: B_def)
    qed
  qed
  have basisB: "vs.basis B" by (rule vs.basisI[OF spanB indB])
  have cardB: "card B = d"
    unfolding B_def by (simp add: card_image[OF power_inj])
  show ?thesis
    using vs.dimension_eq_any_field[OF basisB] cardB by (simp add: d_def)
qed

end (* subfield_tower *)

subsection \<open>The tower law (Steinitz-free, for a two-step simple tower)\<close>

text \<open>For a two-step tower \<open>K \<subseteq> K(a) \<subseteq> K(a)(b)\<close> the products \<open>a\<^sup>i b\<^sup>j\<close> (with \<open>i\<close> below
  \<open>ext_degree K a\<close> and \<open>j\<close> below \<open>ext_degree (eval_img K a) b\<close>) form a \<open>K\<close>-basis of \<open>K(a)(b)\<close>: the
  degrees \<^emph>\<open>multiply\<close>.  We prove the two basis properties directly from the power bases of the two
  simple steps, so no dimension-uniqueness (Steinitz) lemma is needed.\<close>

text \<open>\<^emph>\<open>Spanning.\<close>  Every element of \<open>K(a)(b)\<close> is a \<open>K\<close>-combination of the products \<open>a\<^sup>i b\<^sup>j\<close>.
  Expand along the power basis of \<open>K(a)(b)\<close> over \<open>K(a)\<close>, then expand each \<open>K(a)\<close>-coordinate along
  the power basis of \<open>K(a)\<close> over \<open>K\<close>.\<close>
lemma tower_power_basis_span:
  assumes K: "Subfield K"
    and alg_a: "algebraic_over K a"
    and alg_b: "algebraic_over (eval_img K a) b"
    and y: "y \<in> eval_img (eval_img K a) b"
  shows "\<exists>c. (\<forall>i < ext_degree K a. \<forall>j < ext_degree (eval_img K a) b. c i j \<in> K) \<and>
             y = (\<Sum>j < ext_degree (eval_img K a) b. \<Sum>i < ext_degree K a. c i j * (a ^ i * b ^ j))"
proof -
  define E where "E = eval_img K a"
  have subE: "Subfield E"
    unfolding E_def by (rule Subfield.subfield_eval_img[OF K alg_a])
  have algbE: "algebraic_over E b" 
    using alg_b by (simp add: E_def)
  have yE: "y \<in> eval_img E b" using y by (simp add: E_def)
  \<comment> \<open>Expand @{term y} along the power basis of \<open>E(b)\<close> over @{term E}.\<close>
  obtain c where cE: "\<And>j. j < ext_degree E b \<Longrightarrow> c j \<in> E"
    and yc: "y = (\<Sum>j < ext_degree E b. c j * b ^ j)"
    using Subfield.power_basis_span[OF subE algbE yE] by auto
  \<comment> \<open>Each @{term E}-coordinate expands along the power basis of @{term E} over @{term K}.\<close>
  have Hall: "\<forall>j \<in> {..<ext_degree E b}.
          \<exists>cc. (\<forall>i < ext_degree K a. cc i \<in> K) \<and> c j = (\<Sum>i < ext_degree K a. cc i * a ^ i)"
  proof
    fix j assume "j \<in> {..<ext_degree E b}"
    then have "c j \<in> eval_img K a" using cE by (simp add: E_def)
    then show "\<exists>cc. (\<forall>i < ext_degree K a. cc i \<in> K) \<and> c j = (\<Sum>i < ext_degree K a. cc i * a ^ i)"
      by (rule Subfield.power_basis_span[OF K alg_a])
  qed
  then obtain CC
    where CC: "\<forall>j \<in> {..<ext_degree E b}.
                 (\<forall>i < ext_degree K a. CC j i \<in> K) \<and> c j = (\<Sum>i < ext_degree K a. CC j i * a ^ i)"
    by metis
  \<comment> \<open>Substitute and regroup into a double sum over the products \<open>a\<^sup>i b\<^sup>j\<close>.\<close>
  have "y = (\<Sum>j < ext_degree E b. c j * b ^ j)" by (rule yc)
  also have "\<dots> = (\<Sum>j < ext_degree E b. (\<Sum>i < ext_degree K a. CC j i * a ^ i) * b ^ j)"
    by (rule sum.cong[OF refl]) (use CC in auto)
  also have "\<dots> = (\<Sum>j < ext_degree E b. \<Sum>i < ext_degree K a. CC j i * (a ^ i * b ^ j))"
    by (auto simp: sum_distrib_right mult.assoc)
  finally have yeq: "y = (\<Sum>j < ext_degree E b. \<Sum>i < ext_degree K a. CC j i * (a ^ i * b ^ j))" .
  show ?thesis
    using CC by (force simp: E_def yeq)
qed

text \<open>\<^emph>\<open>Independence.\<close>  A vanishing \<open>K\<close>-combination of the products \<open>a\<^sup>i b\<^sup>j\<close> is trivial.  Factor
  \<open>b\<^sup>j\<close> out of the inner sum: the coefficients of the \<open>b\<close>-powers are \<open>E\<close>-elements, so they vanish
  by independence over @{term E}; each is itself a \<open>K\<close>-combination of the \<open>a\<close>-powers, so its
  coefficients vanish by independence over @{term K}.\<close>
lemma tower_power_basis_indep:
  assumes K: "Subfield K"
    and alg_a: "algebraic_over K a"
    and alg_b: "algebraic_over (eval_img K a) b"
    and cK: "\<And>i j. i < ext_degree K a \<Longrightarrow> j < ext_degree (eval_img K a) b \<Longrightarrow> c i j \<in> K"
    and zero: "(\<Sum>j < ext_degree (eval_img K a) b.
                  \<Sum>i < ext_degree K a. c i j * (a ^ i * b ^ j)) = 0"
  shows "\<forall>i < ext_degree K a. \<forall>j < ext_degree (eval_img K a) b. c i j = 0"
proof -
  define E where "E = eval_img K a"
  have subE: "Subfield E" unfolding E_def by (rule Subfield.subfield_eval_img[OF K alg_a])
  have algbE: "algebraic_over E b" using alg_b by (simp add: E_def)
  have aE: "a \<in> E" unfolding E_def by (rule Subfield.eval_img_self[OF K])
  have cK': "\<And>i j. i < ext_degree K a \<Longrightarrow> j < ext_degree E b \<Longrightarrow> c i j \<in> K"
    using cK by (simp add: E_def)
  define e where "e = (\<lambda>j. \<Sum>i < ext_degree K a. c i j * a ^ i)"
  \<comment> \<open>Each @{term "e j"} is an element of @{term E} (a @{term K}-combination of powers of @{term a}).\<close>
  have eE: "e j \<in> E" if j: "j < ext_degree E b" for j
    unfolding e_def
  proof (rule Subfield.sum_closed[OF subE])
    fix i assume "i \<in> {..<ext_degree K a}"
    then have i: "i < ext_degree K a" by simp
    have "c i j \<in> K" using cK'[OF i j] .
    then have "c i j \<in> E" unfolding E_def
      by (simp add: K Subfield.eval_img_base)
    with aE subE show "c i j * a ^ i \<in> E"
      by (simp add: Subfield.mult_closed Subfield.power_closed)
  qed
  \<comment> \<open>Rewrite the double sum by factoring \<open>b\<^sup>j\<close> out of each inner sum.\<close>
  have "(\<Sum>j < ext_degree E b. e j * b ^ j)
      = (\<Sum>j < ext_degree E b. \<Sum>i < ext_degree K a. c i j * (a ^ i * b ^ j))"
    by (simp add:e_def mult.assoc sum_distrib_right)
  then have esum0: "(\<Sum>j < ext_degree E b. e j * b ^ j) = 0"
    using zero by (simp add: E_def)
  \<comment> \<open>Independence over @{term E} kills every @{term "e j"}.\<close>
  have ej0: "\<forall>j < ext_degree E b. e j = 0"
    using Subfield.power_basis_indep[OF subE algbE eE esum0] .
  \<comment> \<open>Independence over @{term K} then kills every coefficient.\<close>
  show ?thesis
  proof (intro allI impI)
    fix i j assume i: "i < ext_degree K a" and j: "j < ext_degree (eval_img K a) b"
    then have e: "e j = 0" using ej0 by (simp add: E_def)
    have mem: "\<And>i. i < ext_degree K a \<Longrightarrow> c i j \<in> K" 
      using cK j by blast
    have "\<forall>i < ext_degree K a. c i j = 0"
      using Subfield.power_basis_indep[OF K alg_a mem] e by (simp add: e_def)
    then show "c i j = 0" using i by simp
  qed
qed

end
