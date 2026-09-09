section \<open>Primitive elements of finite field extensions\<close>

theory Primitive_Element
  imports Algebraic_Transitivity Extension_Properties Field_Mult_Cyclic Galois_Transitivity
begin

text \<open>
  A primitive element is an element whose simple extension is the whole target field.  The
  definition is deliberately just the equality with @{const eval_img}: the hypotheses that make
  this set a field belong to the surrounding extension theorem, rather than being hidden in the
  predicate itself.
\<close>

definition primitive_element ::
    "'a :: field set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "primitive_element K L a \<longleftrightarrow> L = eval_img K a"

lemma primitive_elementI:
  "L = eval_img K a \<Longrightarrow> primitive_element K L a"
  by (simp add: primitive_element_def)

lemma primitive_elementD:
  "primitive_element K L a \<Longrightarrow> L = eval_img K a"
  by (simp add: primitive_element_def)

lemma primitive_element_mem:
  assumes prim: "primitive_element K L a" and K: "Subfield K"
  shows "a \<in> L"
  using primitive_elementD[OF prim] Subfield.eval_img_self[OF K] by simp

lemma primitive_element_base:
  assumes prim: "primitive_element K L a" and K: "Subfield K"
  shows "K \<subseteq> L"
  using primitive_elementD[OF prim]
    Subfield.eval_img_base[OF K] by blast

subsection \<open>The two-generator theorem over an infinite base\<close>

text \<open>
  The classical separating-linear-combination argument is the substantive core of the primitive
  element theorem.  For separable algebraic elements \<open>a\<close> and \<open>b\<close>, only finitely many
  scalars \<open>c\<close> can make two distinct pairs of conjugates have the same value under
  \<open>(x,y) \<mapsto> x + c*y\<close>.  An infinite base field therefore supplies a scalar outside that
  exceptional set.  The resulting element \<open>a + c*b\<close> recovers both generators.
\<close>
theorem primitive_element_two_generators:
  fixes F :: "'a :: alg_closed_field set"
  assumes sfF: "Subfield F" and infF: "infinite F"
    and alg_a: "algebraic_over F a" and alg_b: "algebraic_over F b"
    and sep_a: "rsquarefree (minpoly F a)" and sep_b: "rsquarefree (minpoly F b)"
  shows "\<exists>theta. eval_img (eval_img F a) b = eval_img F theta"
proof -
  define p where "p = minpoly F a"
  define q where "q = minpoly F b"
  define A where "A = {x. poly p x = 0}"
  define B where "B = {y. poly q y = 0}"
  define C where "C = {(x - a) / (b - y) |x y. x \<in> A \<and> y \<in> B \<and> y \<noteq> b}"
  have p0: "p \<noteq> 0" and q0: "q \<noteq> 0"
    unfolding p_def q_def
    using Subfield.minpoly_nonzero[OF sfF alg_a] Subfield.minpoly_nonzero[OF sfF alg_b]
    by blast+
  have finA: "finite A" and finB: "finite B"
    unfolding A_def B_def using p0 q0 poly_roots_finite by blast+
  have finC: "finite C"
    unfolding C_def
    by (rule finite_subset[of _ "(\<lambda>(x,y). (x-a)/(b-y)) ` (A \<times> B)"])
       (use finA finB in auto)
  have "\<not> F \<subseteq> C"
  proof
    assume "F \<subseteq> C"
    then have "finite F" using finC by (rule finite_subset)
    then show False using infF by contradiction
  qed
  then obtain c where cF: "c \<in> F" and cnot: "c \<notin> C" by blast
  define theta where "theta = a + c * b"

  have unique:
    "x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> theta = x + c * y \<Longrightarrow> x = a \<and> y = b"
    for x y
  proof (cases "y = b")
    case True
    assume xA: "x \<in> A" and yB: "y \<in> B" and eq: "theta = x + c * y"
    have "x = a" using eq True unfolding theta_def by algebra
    then show ?thesis using True by blast
  next
    case False
    assume xA: "x \<in> A" and yB: "y \<in> B" and eq: "theta = x + c * y"
    have den: "b - y \<noteq> 0" using False by simp
    have mult_eq: "c * (b-y) = x-a"
      using eq unfolding theta_def by algebra
    have ceq: "c = (x-a)/(b-y)"
    proof -
      have "c = (c * (b-y)) * inverse (b-y)" using den by simp
      also have "... = (x-a) * inverse (b-y)" by (simp add: mult_eq)
      also have "... = (x-a)/(b-y)" by (simp add: divide_inverse)
      finally show ?thesis .
    qed
    have "c \<in> C"
      unfolding C_def using xA yB False ceq by blast
    then show ?thesis using cnot by blast
  qed

  have alg_theta: "algebraic_over F theta"
  proof -
    interpret Alg: Subfield "algebraic_elements F"
      by (rule subfield_algebraic_elements[OF sfF])
    have aA: "a \<in> algebraic_elements F" and bA: "b \<in> algebraic_elements F"
      using alg_a alg_b by (simp_all add: algebraic_elements_def)
    have cA: "c \<in> algebraic_elements F"
      using Subfield.algebraic_over_self[OF sfF cF]
      by (simp add: algebraic_elements_def)
    have "theta \<in> algebraic_elements F"
      unfolding theta_def by (rule Alg.add_closed[OF aA Alg.mult_closed[OF cA bA]])
    then show ?thesis by (simp add: algebraic_elements_def)
  qed
  define E where "E = eval_img F theta"
  have sfE: "Subfield E"
    unfolding E_def by (rule Subfield.subfield_eval_img[OF sfF alg_theta])
  have FE: "F \<subseteq> E"
    unfolding E_def using Subfield.eval_img_base[OF sfF] by blast
  have thetaE: "theta \<in> E"
    unfolding E_def by (rule Subfield.eval_img_self[OF sfF])
  have cE: "c \<in> E" using cF FE by blast
  have alg_bE: "algebraic_over E b"
    by (rule algebraic_over_mono[OF alg_b FE])
  define m where "m = minpoly E b"
  have m_min: "is_minpoly E b m"
    unfolding m_def by (rule Subfield.is_minpoly_minpoly[OF sfE alg_bE])
  have mE: "m \<in> poly_over E" and mroot: "poly m b = 0" and m0: "m \<noteq> 0"
    using m_min by (auto simp: is_minpoly_def)
  have qE: "q \<in> poly_over E"
    unfolding q_def
    using Subfield.minpoly_over[OF sfF alg_b] poly_over_mono[OF FE] by blast
  have mq: "m dvd q"
    by (rule Subfield.minpoly_dvd[OF sfE m_min qE])
       (simp add: q_def Subfield.minpoly_root[OF sfF alg_b])
  have sep_m: "rsquarefree m"
    by (rule rsquarefree_dvd[OF mq sep_b[folded q_def]])

  have every_root: "poly m r = 0 \<Longrightarrow> r = b" for r
  proof -
    assume mr: "poly m r = 0"
    interpret Id: field_hom_on E "\<lambda>x. x" by (rule field_hom_on_id[OF sfE])
    have mapm: "map_poly (\<lambda>x. x) m = m"
      by (intro poly_eqI) (simp add: coeff_map_poly)
    have rootmap: "poly (map_poly (\<lambda>x. x) m) r = 0"
      unfolding mapm by (rule mr)
    have ex_h: "\<exists>h. field_hom_on (eval_img E b) h \<and> h b = r \<and> (\<forall>x\<in>E. h x = x)"
      by (rule Id.iso_extension[OF alg_bE m_min rootmap])
    obtain h where h: "field_hom_on (eval_img E b) h" "h b = r" "\<forall>x\<in>E. h x = x"
      using ex_h by blast
    interpret H: field_hom_on "eval_img E b" h by (rule h(1))
    have EL: "E \<subseteq> eval_img E b"
      using Subfield.eval_img_base[OF sfE] by blast
    have bL: "b \<in> eval_img E b" by (rule Subfield.eval_img_self[OF sfE])
    have thetaL: "theta \<in> eval_img E b" using thetaE EL by blast
    have cL: "c \<in> eval_img E b" using cE EL by blast
    have aeq: "a = theta - c*b" unfolding theta_def by algebra
    have aL: "a \<in> eval_img E b"
      unfolding aeq by (rule H.diff_closed[OF thetaL H.mult_closed[OF cL bL]])
    have ha: "h a = theta - c*r"
      unfolding aeq
      using H.hom_diff[OF thetaL H.mult_closed[OF cL bL]] H.hom_mult[OF cL bL] h(2,3)
        thetaE cE by simp
    have FL: "F \<subseteq> eval_img E b" using FE EL by blast
    have hfixF: "\<And>x. x \<in> F \<Longrightarrow> h x = x" using h(3) FE by blast
    have pF: "p \<in> poly_over F"
      unfolding p_def by (rule Subfield.minpoly_over[OF sfF alg_a])
    have pa: "poly p a = 0"
      unfolding p_def by (rule Subfield.minpoly_root[OF sfF alg_a])
    have proot_h: "poly p (h a) = 0"
      by (rule hom_preserves_roots[OF h(1) sfF FL hfixF pF aL pa])
    have proot: "poly p (theta - c*r) = 0"
      by (subst ha[symmetric], rule proot_h)
    obtain s where qs: "q = m * s" using mq by (elim dvdE)
    have qr: "poly q r = 0"
    proof -
      have "poly q r = poly (m*s) r" by (simp only: qs)
      also have "... = poly m r * poly s r" by (simp only: poly_mult)
      also have "... = 0 * poly s r" by (simp only: mr)
      also have "... = 0" by algebra
      finally show ?thesis .
    qed
    have rB: "r \<in> B"
      using qr by (simp only: B_def mem_Collect_eq)
    have xrA: "theta - c*r \<in> A"
      using proot by (simp only: A_def mem_Collect_eq)
    have theta_eq: "theta = (theta-c*r) + c*r" by algebra
    have "theta - c*r = a \<and> r = b"
      by (rule unique[OF xrA rB theta_eq])
    then show "r = b" by (rule conjunct2)
  qed
  have roots_m: "{r. poly m r = 0} = {b}"
  proof (rule set_eqI)
    fix r
    show "r \<in> {r. poly m r = 0} \<longleftrightarrow> r \<in> {b}"
    proof
      assume "r \<in> {r. poly m r = 0}"
      then have "poly m r = 0" by (simp only: mem_Collect_eq)
      then have "r = b" by (rule every_root)
      then show "r \<in> {b}" by (simp only: singleton_iff)
    next
      assume "r \<in> {b}"
      then have "r = b" by (simp only: singleton_iff)
      then show "r \<in> {r. poly m r = 0}"
        using mroot by (simp only: mem_Collect_eq)
    qed
  qed
  have card_m: "card {r. poly m r = 0} = degree m"
    by (rule card_roots_eq_degree_alg_closed[OF m0 sep_m])
  have deg_m: "degree m = 1"
  proof -
    have card_b: "card {b} = 1" by simp
    have "card {b} = degree m"
      using card_m by (simp only: roots_m)
    then show ?thesis using card_b by simp
  qed
  have bE: "b \<in> E"
  proof -
    have "ext_degree E b = 1"
      using deg_m by (simp add: ext_degree_def m_def)
    then show ?thesis
      by (rule iffD1[OF Subfield.ext_degree_eq_1_iff[OF sfE alg_bE]])
  qed
  have aE: "a \<in> E"
  proof -
    have cbE: "c*b \<in> E" by (rule Subfield.mult_closed[OF sfE cE bE])
    have diffE: "theta-c*b \<in> E" by (rule Subfield.diff_closed[OF sfE thetaE cbE])
    have "theta-c*b = a" unfolding theta_def by (rule add_diff_cancel_right')
    then show ?thesis using diffE by simp
  qed

  have double_gen:
      "eval_img (eval_img F a) b = generate_field (F \<union> {a,b})"
  proof -
    have sfFa: "Subfield (eval_img F a)"
      by (rule Subfield.subfield_eval_img[OF sfF alg_a])
    have FFa: "F \<subseteq> eval_img F a"
      using Subfield.eval_img_base[OF sfF] by blast
    have alg_bFa: "algebraic_over (eval_img F a) b"
      by (rule algebraic_over_mono[OF alg_b FFa])
    have "eval_img (eval_img F a) b = generate_field (eval_img F a \<union> {b})"
      by (rule Subfield.eval_img_eq_generate_field[OF sfFa alg_bFa])
    also have "... = generate_field (generate_field (F \<union> {a}) \<union> {b})"
      by (simp add: Subfield.eval_img_eq_generate_field[OF sfF alg_a])
    also have "... = generate_field ((F \<union> {a}) \<union> {b})"
      by (rule generate_field_Un_collapse1)
    also have "... = generate_field (F \<union> {a,b})"
      by (rule arg_cong[where f=generate_field]) auto
    finally show ?thesis .
  qed
  have gen_subset_E: "generate_field (F \<union> {a,b}) \<subseteq> E"
    by (rule generate_field_least[OF sfE]) (use FE aE bE in auto)
  have theta_double: "theta \<in> generate_field (F \<union> {a,b})"
  proof -
    interpret G: Subfield "generate_field (F \<union> {a,b})" by (rule subfield_generate_field)
    have aG: "a \<in> generate_field (F \<union> {a,b})" by auto
    have bG: "b \<in> generate_field (F \<union> {a,b})" by auto
    have cG: "c \<in> generate_field (F \<union> {a,b})" using cF by auto
    show ?thesis unfolding theta_def by (rule G.add_closed[OF aG G.mult_closed[OF cG bG]])
  qed
  have E_subset_gen: "E \<subseteq> generate_field (F \<union> {a,b})"
  proof -
    have "E = generate_field (F \<union> {theta})"
      unfolding E_def by (rule Subfield.eval_img_eq_generate_field[OF sfF alg_theta])
    also have "... \<subseteq> generate_field (F \<union> {a,b})"
      by (rule generate_field_least[OF subfield_generate_field])
         (use theta_double in auto)
    finally show ?thesis .
  qed
  have "generate_field (F \<union> {a,b}) = E"
    using gen_subset_E E_subset_gen by blast
  then show ?thesis unfolding double_gen E_def by blast
qed

subsection \<open>Finite separable extensions are simple\<close>

text \<open>
  Over an infinite base, a finite algebraic generating set can be collapsed one generator at a
  time.  Separability is asked of the containing extension, so it applies both to the next
  generator and to the primitive element already obtained for the preceding generators.
\<close>
lemma finite_separable_generators_primitive:
  fixes K L A :: "'a :: alg_closed_field set"
  assumes T: "finite_subfield_tower K L"
    and infK: "infinite K" and finA: "finite A" and AL: "A \<subseteq> L"
    and sep: "separable_extension L K"
  shows "\<exists>theta\<in>L. generate_field (K \<union> A) = eval_img K theta"
proof -
  interpret T: finite_subfield_tower K L by (rule T)
  from finA AL show ?thesis
proof (induction A rule: finite_induct)
  case empty
  have genK: "generate_field K = K"
    using generate_field_least[OF T.base.Subfield_axioms subset_refl]
      subset_generate_field[of K] by blast
  have alg0: "algebraic_over K (0 :: 'a)"
    by (rule T.base.algebraic_over_self) (rule T.base.zero_closed)
  have eval0: "eval_img K 0 = K"
  proof -
    have "eval_img K 0 = generate_field (K \<union> {0})"
      by (rule T.base.eval_img_eq_generate_field[OF alg0])
    also have "... = generate_field K"
      by (rule arg_cong[where f=generate_field]) (use T.base.zero_closed in auto)
    also have "... = K" by (rule genK)
    finally show ?thesis .
  qed
  show ?case using T.ext.zero_closed genK eval0 by auto
next
  case (insert a A)
  have aL: "a \<in> L" and AL: "A \<subseteq> L" using insert.prems by auto
  obtain theta where thetaL: "theta \<in> L"
    and genA: "generate_field (K \<union> A) = eval_img K theta"
    using insert.IH[OF AL] by blast
  have alg_a: "algebraic_over K a" by (rule T.finite_extension_algebraic[OF aL])
  have alg_theta: "algebraic_over K theta"
    by (rule T.finite_extension_algebraic[OF thetaL])
  have sep_a: "rsquarefree (minpoly K a)"
    by (rule separable_extensionD[OF sep aL alg_a])
  have sep_theta: "rsquarefree (minpoly K theta)"
    by (rule separable_extensionD[OF sep thetaL alg_theta])
  obtain z where pair:
      "eval_img (eval_img K theta) a = eval_img K z"
    using primitive_element_two_generators[OF T.base.Subfield_axioms infK alg_theta alg_a
      sep_theta sep_a] by blast
  have sfKtheta: "Subfield (eval_img K theta)"
    by (rule T.base.subfield_eval_img[OF alg_theta])
  have Ktheta: "K \<subseteq> eval_img K theta"
    using T.base.eval_img_base by blast
  have alg_a_theta: "algebraic_over (eval_img K theta) a"
    by (rule algebraic_over_mono[OF alg_a Ktheta])
  have generated_insert:
      "generate_field (K \<union> insert a A) = eval_img (eval_img K theta) a"
  proof -
    have set_eq: "K \<union> insert a A = (K \<union> A) \<union> {a}" by auto
    have "generate_field (K \<union> insert a A) = generate_field ((K \<union> A) \<union> {a})"
      by (rule arg_cong[OF set_eq])
    also have "... = generate_field (generate_field (K \<union> A) \<union> {a})"
      by (rule sym, rule generate_field_Un_collapse1)
    also have "... = generate_field (eval_img K theta \<union> {a})"
      by (simp only: genA)
    also have "... = eval_img (eval_img K theta) a"
      by (rule sym, rule Subfield.eval_img_eq_generate_field[OF sfKtheta alg_a_theta])
    finally show ?thesis .
  qed
  have generated_subset_L: "generate_field (K \<union> insert a A) \<subseteq> L"
    by (rule generate_field_least[OF T.ext.Subfield_axioms])
       (use T.base_subset aL AL in auto)
  have z_eval: "z \<in> eval_img K z" by (rule T.base.eval_img_self)
  have zL: "z \<in> L"
    using z_eval pair generated_insert generated_subset_L by blast
  show ?case using zL generated_insert pair by blast
qed
qed

text \<open>
  Finite fields have a particularly clean primitive-element proof.  The multiplicative group of
  the target field is cyclic, so a generator of its nonzero elements already generates the field
  as a simple extension over every subfield.  This is the finite-field instance of the primitive
  element theorem and is the useful bridge for the concrete finite-field theories.
\<close>

theorem finite_field_extension_is_simple:
  assumes KL: "subfield_tower K L" and finL: "finite L"
  shows "\<exists>a\<in>L. primitive_element K L a"
proof -
  interpret KL: subfield_tower K L by (rule KL)
  interpret Lf: Field L "(+)" "(*)" "0" "1"
    by (rule Subfield.sf_field[OF KL.ext.Subfield_axioms])
  interpret G: Group Lf.Fstar "(*)" "1" by (rule Lf.Group_Fstar)
  have finstar: "finite Lf.Fstar"
    by (simp add: Lf.Fstar_def finL)
  obtain g where gstar: "g \<in> Lf.Fstar"
    and cyc: "G.cyclic_subgroup g = Lf.Fstar"
    using Lf.finite_field_mult_cyclic[OF finstar] by blast
  have gL: "g \<in> L" using gstar by (simp add: Lf.Fstar_def)
  have gpow: "G.power g n \<in> eval_img K g" for n
  proof (induction n)
    case 0
    show ?case by (simp add: Subfield.eval_img_1[OF KL.base.Subfield_axioms])
  next
    case (Suc n)
    have gE: "g \<in> eval_img K g"
      by (rule Subfield.eval_img_self[OF KL.base.Subfield_axioms])
    have "g * G.power g n \<in> eval_img K g"
      by (rule Subfield.eval_img_mult[OF KL.base.Subfield_axioms gE Suc.IH])
    then show ?case by (simp add: G.power_Suc)
  qed
  have L_subset: "L \<subseteq> eval_img K g"
  proof
    fix x assume xL: "x \<in> L"
    show "x \<in> eval_img K g"
    proof (cases "x = 0")
      case True
      then show ?thesis by (simp add: Subfield.eval_img_0[OF KL.base.Subfield_axioms])
    next
      case False
      have xstar: "x \<in> Lf.Fstar" using xL False by (simp add: Lf.Fstar_def)
      have xcyc: "x \<in> G.cyclic_subgroup g" using xstar by (simp add: cyc)
      obtain n where "x = G.power g n"
        using G.cyclic_subgroup_eq_range[OF finstar gstar] xcyc by blast
      then show ?thesis using gpow by simp
    qed
  qed
  have E_subset: "eval_img K g \<subseteq> L"
  proof
    fix x assume xE: "x \<in> eval_img K g"
    obtain p where pK: "p \<in> poly_over K" and x: "x = poly p g"
      using xE by (rule eval_imgE)
    have xG: "x \<in> generate_field (K \<union> {g})"
      unfolding x
      by (rule Subfield.eval_img_subset_generate_field[OF KL.base.Subfield_axioms pK])
    have KG: "K \<union> {g} \<subseteq> L"
      using KL.base_subset gL by blast
    have Gsub: "generate_field (K \<union> {g}) \<subseteq> L"
      by (rule generate_field_least[OF KL.ext.Subfield_axioms KG])
    show "x \<in> L" using Gsub xG by blast
  qed
  have eq: "L = eval_img K g" using L_subset E_subset by (rule subset_antisym)
  show ?thesis using gL primitive_elementI[OF eq] by blast
qed

text \<open>
  The full primitive-element theorem now follows from a basis.  If the base is finite, the finite
  coordinate space makes the target field finite and the multiplicative-cyclic proof applies.  If
  the base is infinite, the preceding finite-generator theorem collapses the basis to one element.
\<close>
theorem finite_separable_extension_is_simple:
  fixes K L :: "'a :: alg_closed_field set"
  assumes T: "finite_subfield_tower K L" and sep: "separable_extension L K"
  shows "\<exists>a\<in>L. primitive_element K L a"
proof -
  interpret T: finite_subfield_tower K L by (rule T)
  show ?thesis
  proof (cases "finite K")
    case True
    obtain B where basis: "T.vs.basis B" using T.finite_basis by blast
    have finB: "finite B" using basis by (simp add: T.vs.basis_def)
    have bij: "bij_betw (\<lambda>c. T.vs.lincomb c B) (B \<rightarrow>\<^sub>E K) L"
      using basis by (simp add: T.vs.basis_def)
    have fin_coords: "finite (B \<rightarrow>\<^sub>E K)"
      by (rule finite_PiE[OF finB]) (use True in auto)
    have finL: "finite L"
      using bij_betw_finite[OF bij] fin_coords by blast
    show ?thesis
      by (rule finite_field_extension_is_simple[OF T.subfield_tower_axioms finL])
  next
    case False
    then have infK: "infinite K" by simp
    obtain B where basis: "T.vs.basis B" using T.finite_basis by blast
    have finB: "finite B" and BL: "B \<subseteq> L"
      using basis by (auto simp: T.vs.basis_def)
    have gen_subset: "generate_field (K \<union> B) \<subseteq> L"
      by (rule generate_field_least[OF T.ext.Subfield_axioms]) (use T.base_subset BL in auto)
    have L_subset: "L \<subseteq> generate_field (K \<union> B)"
    proof
      fix x assume xL: "x \<in> L"
      obtain c where c: "c \<in> B \<rightarrow>\<^sub>E K" "x = T.vs.lincomb c B"
        using T.vs.basis_spanning[OF basis] xL
        unfolding T.vs.spanning_def by blast
      have cK: "\<And>v. v \<in> B \<Longrightarrow> c v \<in> K" using c(1) by auto
      have lincomb_sum: "T.vs.lincomb c B = (\<Sum>v\<in>B. c v * v)"
        by (rule T.vs_lincomb_eq_sum[OF finB BL cK])
      interpret G: Subfield "generate_field (K \<union> B)" by (rule subfield_generate_field)
      have sumG: "(\<Sum>v\<in>B. c v * v) \<in> generate_field (K \<union> B)"
        by (rule G.sum_closed, rule G.mult_closed) (use cK in auto)
      show "x \<in> generate_field (K \<union> B)"
        using c(2) lincomb_sum sumG by simp
    qed
    have Lgen: "L = generate_field (K \<union> B)"
      by (rule subset_antisym[OF L_subset gen_subset])
    obtain theta where thetaL: "theta \<in> L"
      and prim: "generate_field (K \<union> B) = eval_img K theta"
      using finite_separable_generators_primitive[OF T infK finB BL sep] by blast
    have "L = eval_img K theta" using Lgen prim by simp
    then show ?thesis using thetaL primitive_elementI by blast
  qed
qed

lemma (in finite_subfield_tower) primitive_element_degree:
  assumes prim: "primitive_element K L a"
  shows "extension_degree = ext_degree K a"
proof -
  have aL: "a \<in> L"
    using primitive_element_mem[OF prim base.Subfield_axioms] .
  have alg: "algebraic_over K a" by (rule finite_extension_algebraic[OF aL])
  show ?thesis
    using extension_degree_eq_ext_degree[OF alg primitive_elementD[OF prim]] .
qed

end
