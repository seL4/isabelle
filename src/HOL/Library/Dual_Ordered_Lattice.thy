(*  Title:      Dual_Ordered_Lattice.thy
    Authors:    Makarius; Peter Gammie; Brian Huffman; Florian Haftmann, TU Muenchen
*)

section \<open>Type of dual ordered lattices\<close>

theory Dual_Ordered_Lattice
imports Main
begin

text \<open>
  The \<^emph>\<open>dual\<close> of an ordered structure is an isomorphic copy of the
  underlying type, with the \<open>\<le>\<close> relation defined as the inverse
  of the original one.

  The class of lattices is closed under formation of dual structures.
  This means that for any theorem of lattice theory, the dualized
  statement holds as well; this important fact simplifies many proofs
  of lattice theory.
\<close>

typedef 'a dual = "UNIV :: 'a set"
  morphisms undual dual ..

setup_lifting type_definition_dual

lemma dual_eqI:
  "x = y" if "undual x = undual y"
  using that by transfer assumption

lemma dual_eq_iff:
  "x = y \<longleftrightarrow> undual x = undual y"
  by transfer simp

lemma eq_dual_iff [iff]:
  "dual x = dual y \<longleftrightarrow> x = y"
  by transfer simp

lemma undual_dual [simp]:
  "undual (dual x) = x"
  by transfer rule

lemma dual_undual [simp]:
  "dual (undual x) = x"
  by transfer rule

lemma undual_comp_dual [simp]:
  "undual \<circ> dual = id"
  by (simp add: fun_eq_iff)

lemma dual_comp_undual [simp]:
  "dual \<circ> undual = id"
  by (simp add: fun_eq_iff)

lemma inj_dual:
  "inj dual"
  by (rule injI) simp

lemma inj_undual:
  "inj undual"
  by (rule injI) (rule dual_eqI)

lemma surj_dual:
  "surj dual"
  by (rule surjI [of _ undual]) simp

lemma surj_undual:
  "surj undual"
  by (rule surjI [of _ dual]) simp

lemma bij_dual:
  "bij dual"
  using inj_dual surj_dual by (rule bijI)

lemma bij_undual:
  "bij undual"
  using inj_undual surj_undual by (rule bijI)

instance dual :: (finite) finite
proof
  from finite have "finite (range dual :: 'a dual set)"
    by (rule finite_imageI)
  then show "finite (UNIV :: 'a dual set)"
    by (simp add: surj_dual)
qed


subsection \<open>Pointwise ordering\<close>

instantiation dual :: (ord) ord
begin

lift_definition less_eq_dual :: "'a dual \<Rightarrow> 'a dual \<Rightarrow> bool"
  is "(\<ge>)" .

lift_definition less_dual :: "'a dual \<Rightarrow> 'a dual \<Rightarrow> bool"
  is "(>)" .

instance ..

end

lemma dual_less_eqI:
  "x \<le> y" if "undual y \<le> undual x"
  using that by transfer assumption

lemma dual_less_eq_iff:
  "x \<le> y \<longleftrightarrow> undual y \<le> undual x"
  by transfer simp

lemma less_eq_dual_iff [iff]:
  "dual x \<le> dual y \<longleftrightarrow> y \<le> x"
  by transfer simp

lemma dual_lessI:
  "x < y" if "undual y < undual x"
  using that by transfer assumption

lemma dual_less_iff:
  "x < y \<longleftrightarrow> undual y < undual x"
  by transfer simp

lemma less_dual_iff [iff]:
  "dual x < dual y \<longleftrightarrow> y < x"
  by transfer simp

instance dual :: (preorder) preorder
  by (standard; transfer) (auto simp add: less_le_not_le intro: order_trans)

instance dual :: (order) order
  by (standard; transfer) simp


subsection \<open>Binary infimum and supremum\<close>

instantiation dual :: (sup) inf
begin

lift_definition inf_dual :: "'a dual \<Rightarrow> 'a dual \<Rightarrow> 'a dual"
  is sup .

instance ..

end

lemma undual_inf_eq [simp]:
  "undual (inf x y) = sup (undual x) (undual y)"
  by (fact inf_dual.rep_eq)

lemma dual_sup_eq [simp]:
  "dual (sup x y) = inf (dual x) (dual y)"
  by transfer rule

instantiation dual :: (inf) sup
begin

lift_definition sup_dual :: "'a dual \<Rightarrow> 'a dual \<Rightarrow> 'a dual"
  is inf .

instance ..

end

lemma undual_sup_eq [simp]:
  "undual (sup x y) = inf (undual x) (undual y)"
  by (fact sup_dual.rep_eq)

lemma dual_inf_eq [simp]:
  "dual (inf x y) = sup (dual x) (dual y)"
  by transfer simp

instance dual :: (semilattice_sup) semilattice_inf
  by (standard; transfer) simp_all

instance dual :: (semilattice_inf) semilattice_sup
  by (standard; transfer) simp_all

instance dual :: (lattice) lattice ..

instance dual :: (distrib_lattice) distrib_lattice
  by (standard; transfer) (fact inf_sup_distrib1)


subsection \<open>Top and bottom elements\<close>

instantiation dual :: (top) bot
begin

lift_definition bot_dual :: "'a dual"
  is top .

instance ..

end

lemma undual_bot_eq [simp]:
  "undual bot = top"
  by (fact bot_dual.rep_eq)

lemma dual_top_eq [simp]:
  "dual top = bot"
  by transfer rule

instantiation dual :: (bot) top
begin

lift_definition top_dual :: "'a dual"
  is bot .

instance ..

end

lemma undual_top_eq [simp]:
  "undual top = bot"
  by (fact top_dual.rep_eq)

lemma dual_bot_eq [simp]:
  "dual bot = top"
  by transfer rule

instance dual :: (order_top) order_bot
  by (standard; transfer) simp

instance dual :: (order_bot) order_top
  by (standard; transfer) simp

instance dual :: (bounded_lattice_top) bounded_lattice_bot ..

instance dual :: (bounded_lattice_bot) bounded_lattice_top ..

instance dual :: (bounded_lattice) bounded_lattice ..


subsection \<open>Complement\<close>

instantiation dual :: (uminus) uminus
begin

lift_definition uminus_dual :: "'a dual \<Rightarrow> 'a dual"
  is uminus .

instance ..

end

lemma undual_uminus_eq [simp]:
  "undual (- x) = - undual x"
  by (fact uminus_dual.rep_eq)

lemma dual_uminus_eq [simp]:
  "dual (- x) = - dual x"
  by transfer rule

instantiation dual :: (boolean_algebra) boolean_algebra
begin

lift_definition minus_dual :: "'a dual \<Rightarrow> 'a dual \<Rightarrow> 'a dual"
  is "\<lambda>x y. - (y - x)" .

instance
  by (standard; transfer) (simp_all add: diff_eq ac_simps)

end

lemma undual_minus_eq [simp]:
  "undual (x - y) = - (undual y - undual x)"
  by (fact minus_dual.rep_eq)

lemma dual_minus_eq [simp]:
  "dual (x - y) = - (dual y - dual x)"
  by transfer simp


subsection \<open>Complete lattice operations\<close>

text \<open>
  The class of complete lattices is closed under formation of dual
  structures.
\<close>

instantiation dual :: (Sup) Inf
begin

lift_definition Inf_dual :: "'a dual set \<Rightarrow> 'a dual"
  is Sup .

instance ..

end

lemma undual_Inf_eq [simp]:
  "undual (Inf A) = Sup (undual ` A)"
  by (fact Inf_dual.rep_eq)

lemma dual_Sup_eq [simp]:
  "dual (Sup A) = Inf (dual ` A)"
  by transfer simp

instantiation dual :: (Inf) Sup
begin

lift_definition Sup_dual :: "'a dual set \<Rightarrow> 'a dual"
  is Inf .

instance ..

end

lemma undual_Sup_eq [simp]:
  "undual (Sup A) = Inf (undual ` A)"
  by (fact Sup_dual.rep_eq)

lemma dual_Inf_eq [simp]:
  "dual (Inf A) = Sup (dual ` A)"
  by transfer simp

instance dual :: (complete_lattice) complete_lattice
  by (standard; transfer) (auto intro: Inf_lower Sup_upper Inf_greatest Sup_least)

context
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
    and g :: "'a dual \<Rightarrow> 'a dual"
  assumes "mono f"
  defines "g \<equiv> dual \<circ> f \<circ> undual"
begin

private lemma mono_dual:
  "mono g"
proof
  fix x y :: "'a dual"
  assume "x \<le> y"
  then have "undual y \<le> undual x"
    by (simp add: dual_less_eq_iff)
  with \<open>mono f\<close> have "f (undual y) \<le> f (undual x)"
    by (rule monoD)
  then have "(dual \<circ> f \<circ> undual) x \<le> (dual \<circ> f \<circ> undual) y"
    by simp
  then show "g x \<le> g y"
    by (simp add: g_def)
qed

lemma lfp_dual_gfp:
  "lfp f = undual (gfp g)" (is "?lhs = ?rhs")
proof (rule antisym)
  have "dual (undual (g (gfp g))) \<le> dual (f (undual (gfp g)))"
    by (simp add: g_def)
  with mono_dual have "f (undual (gfp g)) \<le> undual (gfp g)"
    by (simp add: gfp_unfold [where f = g, symmetric] dual_less_eq_iff)
  then show "?lhs \<le> ?rhs"
    by (rule lfp_lowerbound)
  from \<open>mono f\<close> have "dual (lfp f) \<le> dual (undual (gfp g))"
    by (simp add: lfp_fixpoint gfp_upperbound g_def)
  then show "?rhs \<le> ?lhs"
    by (simp only: less_eq_dual_iff)
qed

lemma gfp_dual_lfp:
  "gfp f = undual (lfp g)"
proof -
  have "mono (\<lambda>x. undual (undual x))"
    by (rule monoI)  (simp add: dual_less_eq_iff)
  moreover have "mono (\<lambda>a. dual (dual (f a)))"
    using \<open>mono f\<close> by (auto intro: monoI dest: monoD)
  moreover have "gfp f = gfp (\<lambda>x. undual (undual (dual (dual (f x)))))"
    by simp
  ultimately have "undual (undual (gfp (\<lambda>x. dual
    (dual (f (undual (undual x))))))) =
      gfp (\<lambda>x. undual (undual (dual (dual (f x)))))"
    by (subst gfp_rolling [where g = "\<lambda>x. undual (undual x)"]) simp_all
  then have "gfp f =
    undual
     (undual
       (gfp (\<lambda>x. dual (dual (f (undual (undual x)))))))"
    by simp
  also have "\<dots> = undual (undual (gfp (dual \<circ> g \<circ> undual)))"
    by (simp add: comp_def g_def)
  also have "\<dots> = undual (lfp g)"
    using mono_dual by (simp only: Dual_Ordered_Lattice.lfp_dual_gfp)
  finally show ?thesis .
qed

end


text \<open>Finally\<close>

lifting_update dual.lifting
lifting_forget dual.lifting

end
