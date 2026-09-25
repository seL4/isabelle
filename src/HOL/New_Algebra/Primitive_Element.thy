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

definition primitive_element :: "'a :: field set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "primitive_element K L a \<longleftrightarrow> L = eval_img K a"

lemma primitive_elementI:
  "L = eval_img K a \<Longrightarrow> primitive_element K L a"
  by (simp add: primitive_element_def)

lemma primitive_elementD:
  "primitive_element K L a \<Longrightarrow> L = eval_img K a"
  by (simp add: primitive_element_def)

lemma
  assumes "primitive_element K L a" "Subfield K"
  shows primitive_element_mem: "a \<in> L" and primitive_element_base: "K \<subseteq> L"
  using assms Subfield.eval_img_base Subfield.eval_img_self primitive_elementD by blast+

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
  define p where "p \<equiv> minpoly F a"
  define q where "q \<equiv> minpoly F b"
  define A where "A \<equiv> {x. poly p x = 0}"
  define B where "B \<equiv> {y. poly q y = 0}"
  define C where "C \<equiv> {(x - a) / (b - y) |x y. x \<in> A \<and> y \<in> B \<and> y \<noteq> b}"
  obtain p0: "p \<noteq> 0" and q0: "q \<noteq> 0"
    using p_def q_def rsquarefree_def sep_a sep_b by auto
  have finA: "finite A" and finB: "finite B"
    unfolding A_def B_def using p0 q0 poly_roots_finite by blast+
  then have finC: "finite C"
    unfolding C_def finite_subset[of _ "(\<lambda>(x,y). (x-a)/(b-y)) ` (A \<times> B)"]
    by (simp add: finite_image_set2)
  have "\<not> F \<subseteq> C"
    using finC finite_subset infF by blast
  then obtain c where cF: "c \<in> F" and cnot: "c \<notin> C" by blast
  define theta where "theta = a + c * b"

  have unique: "x = a \<and> y = b" 
    if xA: "x \<in> A" and yB: "y \<in> B" and eq: "theta = x + c * y" for x y
  proof (cases "y = b")
    case True
    then show ?thesis
      using eq theta_def by force
  next
    case False
    then have den: "b - y \<noteq> 0" by simp
    have "c * (b-y) = x-a"
      using eq unfolding theta_def by algebra
    then have ceq: "c = (x-a)/(b-y)"
      using den eq_divide_imp by blast
    then show ?thesis using cnot
      using C_def False xA yB by blast
  qed

  interpret Alg: Subfield "algebraic_elements F"
    by (rule subfield_algebraic_elements[OF sfF])
  have cA: "c \<in> algebraic_elements F"
    by (simp add: Subfield.algebraic_over_self algebraic_elements_def cF sfF)
  then have alg_theta: "algebraic_over F theta"
    using alg_a alg_b algebraic_elements_def theta_def by blast
  define E where "E \<equiv> eval_img F theta"
  have sfE: "Subfield E"
    unfolding E_def by (rule Subfield.subfield_eval_img[OF sfF alg_theta])
  have FE: "F \<subseteq> E"
    unfolding E_def using Subfield.eval_img_base[OF sfF] by blast
  have thetaE: "theta \<in> E"
    unfolding E_def by (rule Subfield.eval_img_self[OF sfF])
  have cE: "c \<in> E" using cF FE by blast
  have alg_bE: "algebraic_over E b"
    by (rule algebraic_over_mono[OF alg_b FE])
  define m where "m \<equiv> minpoly E b"
  have m_min: "is_minpoly E b m"
    unfolding m_def by (rule Subfield.is_minpoly_minpoly[OF sfE alg_bE])
  have mE: "m \<in> poly_over E" and mroot: "poly m b = 0" and m0: "m \<noteq> 0"
    using m_min by (auto simp: is_minpoly_def)
  have qE: "q \<in> poly_over E"
    unfolding q_def
    using Subfield.minpoly_over[OF sfF alg_b] poly_over_mono[OF FE] by blast
  have mq: "m dvd q"
    using Subfield.minpoly_dvd Subfield.minpoly_root alg_b m_min qE q_def sfE sfF by blast

  have every_root: "r = b" if mr: "poly m r = 0" for r
  proof -
    interpret Id: field_hom_on E "\<lambda>x. x" by (rule field_hom_on_id[OF sfE])
    have mapm: "map_poly (\<lambda>x. x) m = m"
      by (intro poly_eqI) (simp add: coeff_map_poly)
    then obtain h where h: "field_hom_on (eval_img E b) h" "h b = r" "\<forall>x\<in>E. h x = x"
      using mr Id.iso_extension[OF alg_bE m_min] by metis
    interpret H: field_hom_on "eval_img E b" h by (rule h(1))
    have EL: "E \<subseteq> eval_img E b"
      using Subfield.eval_img_base[OF sfE] by blast
    have bL: "b \<in> eval_img E b" by (rule Subfield.eval_img_self[OF sfE])
    have thetaL: "theta \<in> eval_img E b" using thetaE EL by blast
    have cL: "c \<in> eval_img E b" using cE EL by blast
    have aeq: "a = theta - c*b" unfolding theta_def by algebra
    have aL: "a \<in> eval_img E b"
      unfolding aeq by (rule H.diff_closed[OF thetaL H.mult_closed[OF cL bL]])
    have FL: "F \<subseteq> eval_img E b" using FE EL by blast
    have hfixF: "\<And>x. x \<in> F \<Longrightarrow> h x = x" using h(3) FE by blast
    obtain pF: "p \<in> poly_over F" and pa: "poly p a = 0"
      using Subfield.minpoly_over Subfield.minpoly_root alg_a p_def sfF by blast
    have proot_h: "poly p (h a) = 0"
      using FL H.field_hom_on_axioms aL hfixF hom_preserves_roots pF pa sfF by blast
    have ha: "theta - c*r = h a"
      by (simp add: H.hom_diff H.hom_mult H.mult_closed aeq bL cE cL h thetaE thetaL)
    then have proot: "poly p (theta - c*r) = 0"
      using proot_h by presburger
    obtain s where qs: "q = m * s" using mq by (elim dvdE)
    have qr: "poly q r = 0"
      using mr qs by (metis mult_zero_left poly_mult)
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
    by (auto simp: every_root mroot)
  have "card {r. poly m r = 0} = degree m"
    using card_roots_eq_degree_alg_closed m0 mq q_def rsquarefree_dvd sep_b by blast
  then have deg_m: "degree m = 1"
    by (simp add: roots_m)
  have "ext_degree E b = 1"
    using deg_m by (simp add: ext_degree_def m_def)
  then have bE: "b \<in> E"
    using Subfield.ext_degree_eq_1_iff alg_bE sfE by blast
  have diffE: "theta-c*b \<in> E"
    by (simp add: Subfield.diff_closed Subfield.mult_closed bE cE sfE thetaE)
  then have aE: "a \<in> E" 
    using theta_def by fastforce
  have double_gen: "eval_img (eval_img F a) b = generate_field (F \<union> {a,b})"
  proof -
    have sfFa: "Subfield (eval_img F a)"
      by (rule Subfield.subfield_eval_img[OF sfF alg_a])
    have alg_bFa: "algebraic_over (eval_img F a) b"
      by (metis alg_b sfF algebraic_over_mono primitive_elementI primitive_element_base)
    have "eval_img (eval_img F a) b =  generate_field (generate_field (F \<union> {a}) \<union> {b})"
      by (metis alg_a alg_bFa sfF sfFa Subfield.eval_img_eq_generate_field)
    also have "... = generate_field (F \<union> {a,b})"
      by (metis Un_insert_left Un_insert_right generate_field_Un_collapse1 sup_bot.right_neutral)
    finally show ?thesis .
  qed
  have gen_subset_E: "generate_field (F \<union> {a,b}) \<subseteq> E"
    by (rule generate_field_least[OF sfE]) (use FE aE bE in auto)
  have theta_double: "theta \<in> generate_field (F \<union> {a,b})"
    using cF theta_def by blast
  have E_subset_gen: "E \<subseteq> generate_field (F \<union> {a,b})"
  proof -
    have "E = generate_field (F \<union> {theta})"
      unfolding E_def by (rule Subfield.eval_img_eq_generate_field[OF sfF alg_theta])
    also have "... \<subseteq> generate_field (F \<union> {a,b})"
      using theta_double
      by (intro generate_field_least[OF subfield_generate_field]) auto
    finally show ?thesis .
  qed
  then show ?thesis unfolding double_gen E_def
    using E_def gen_subset_E by blast
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
    have "eval_img K 0 = generate_field (K \<union> {0})"
      by (simp add: T.base.eval_img_eq_generate_field T.base.algebraic_over_self)
    also have "... =  K"
      by (simp add: T.base.generate_field_self insert_absorb)
    finally have eval0: "eval_img K 0 = K" .
    show ?case using T.ext.zero_closed T.base.generate_field_self eval0 by auto
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
    obtain z where pair: "eval_img (eval_img K theta) a = eval_img K z"
      using primitive_element_two_generators[OF T.base.Subfield_axioms infK alg_theta alg_a
          sep_theta sep_a] by blast
    have sfKtheta: "Subfield (eval_img K theta)"
      by (rule T.base.subfield_eval_img[OF alg_theta])
    have alg_a_theta: "algebraic_over (eval_img K theta) a"
      using T.base.eval_img_base alg_a algebraic_over_mono genA generate_field_mono sup_ge1 by blast
    have "K \<union> insert a A = (K \<union> A) \<union> {a}" by auto
    then have "generate_field (K \<union> insert a A) = generate_field (generate_field (K \<union> A) \<union> {a})"
      by (metis generate_field_Un_collapse1)
    also have "... = eval_img (eval_img K theta) a"
      by (simp add: Subfield.eval_img_eq_generate_field alg_a_theta genA sfKtheta)
    finally have generated_insert:
      "generate_field (K \<union> insert a A) = eval_img (eval_img K theta) a" .
    have generated_subset_L: "generate_field (K \<union> insert a A) \<subseteq> L"
      using generate_field_least[OF T.ext.Subfield_axioms] T.base_subset aL AL by simp
    have "z \<in> eval_img K z" by (rule T.base.eval_img_self)
    then show ?case 
      using pair generated_insert generated_subset_L pair by blast
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
  by (induction n) (auto simp: KL.base.eval_img_1 KL.base.eval_img_mult KL.base.eval_img_self)
  have L_subset: "L \<subseteq> eval_img K g"
  proof
    fix x assume xL: "x \<in> L"
    show "x \<in> eval_img K g"
    proof (cases "x = 0")
      case True
      then show ?thesis by (simp add: Subfield.eval_img_0[OF KL.base.Subfield_axioms])
    next
      case False 
      then obtain n where "x = G.power g n"
        using G.cyclic_subgroup_eq_range[OF finstar gstar] Lf.Fstar_iff cyc xL by blast
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
    show "x \<in> L" using generate_field_least[OF KL.ext.Subfield_axioms KG] xG by blast
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
    then show ?thesis
      by (simp add: T.finite_carrier_of_finite_base T.subfield_tower_axioms
          finite_field_extension_is_simple)
  next
    case False
    then have infK: "infinite K" by simp
    obtain B where basis: "T.vs.basis B" using T.finite_basis by blast
    have finB: "finite B" and BL: "B \<subseteq> L"
      using basis by (auto simp: T.vs.basis_def)
    have Leq_gen: "L = generate_field (K \<union> B)"
      using T.generate_field_basis basis by auto
    obtain theta where "theta \<in> L" and "generate_field (K \<union> B) = eval_img K theta"
      using finite_separable_generators_primitive[OF T infK finB BL sep] by blast
    then show ?thesis using primitive_elementI
      using Leq_gen by blast
  qed
qed

lemma (in finite_subfield_tower) primitive_element_degree:
  assumes "primitive_element K L a"
  shows "extension_degree = ext_degree K a"
proof -
  have aL: "a \<in> L"
    using primitive_element_mem[OF assms base.Subfield_axioms] .
  with assms show ?thesis
    by (simp add: extension_degree_eq_ext_degree finite_extension_algebraic primitive_elementD)
qed

end
