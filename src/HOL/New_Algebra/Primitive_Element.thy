section \<open>Primitive elements of finite field extensions\<close>

theory Primitive_Element
  imports Algebraic_Transitivity Field_Mult_Cyclic
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
