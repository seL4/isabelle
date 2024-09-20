(*  Title:      HOL/Algebra/AbelCoset.thy
    Author:     Stephan Hohe, TU Muenchen
*)

theory AbelCoset
imports Coset Ring
begin

subsection \<open>More Lifting from Groups to Abelian Groups\<close>

subsubsection \<open>Definitions\<close>

text \<open>Hiding \<open><+>\<close> from \<^theory>\<open>HOL.Sum_Type\<close> until I come
  up with better syntax here\<close>

no_notation Sum_Type.Plus (infixr \<open><+>\<close> 65)

definition
  a_r_coset    :: "[_, 'a set, 'a] \<Rightarrow> 'a set"    (infixl \<open>+>\<index>\<close> 60)
  where "a_r_coset G = r_coset (add_monoid G)"

definition
  a_l_coset    :: "[_, 'a, 'a set] \<Rightarrow> 'a set"    (infixl \<open><+\<index>\<close> 60)
  where "a_l_coset G = l_coset (add_monoid G)"

definition
  A_RCOSETS  :: "[_, 'a set] \<Rightarrow> ('a set)set"   (\<open>a'_rcosets\<index> _\<close> [81] 80)
  where "A_RCOSETS G H = RCOSETS (add_monoid G) H"

definition
  set_add  :: "[_, 'a set ,'a set] \<Rightarrow> 'a set" (infixl \<open><+>\<index>\<close> 60)
  where "set_add G = set_mult (add_monoid G)"

definition
  A_SET_INV :: "[_,'a set] \<Rightarrow> 'a set"  (\<open>a'_set'_inv\<index> _\<close> [81] 80)
  where "A_SET_INV G H = SET_INV (add_monoid G) H"

definition
  a_r_congruent :: "[('a,'b)ring_scheme, 'a set] \<Rightarrow> ('a*'a)set"  (\<open>racong\<index>\<close>)
  where "a_r_congruent G = r_congruent (add_monoid G)"

definition
  A_FactGroup :: "[('a,'b) ring_scheme, 'a set] \<Rightarrow> ('a set) monoid" (infixl \<open>A'_Mod\<close> 65)
    \<comment> \<open>Actually defined for groups rather than monoids\<close>
  where "A_FactGroup G H = FactGroup (add_monoid G) H"

definition
  a_kernel :: "('a, 'm) ring_scheme \<Rightarrow> ('b, 'n) ring_scheme \<Rightarrow>  ('a \<Rightarrow> 'b) \<Rightarrow> 'a set"
    \<comment> \<open>the kernel of a homomorphism (additive)\<close>
  where "a_kernel G H h = kernel (add_monoid G) (add_monoid H) h"

locale abelian_group_hom = G?: abelian_group G + H?: abelian_group H
    for G (structure) and H (structure) +
  fixes h
  assumes a_group_hom: "group_hom (add_monoid G) (add_monoid H) h"

lemmas a_r_coset_defs =
  a_r_coset_def r_coset_def

lemma a_r_coset_def':
  fixes G (structure)
  shows "H +> a \<equiv> \<Union>h\<in>H. {h \<oplus> a}"
  unfolding a_r_coset_defs by simp

lemmas a_l_coset_defs =
  a_l_coset_def l_coset_def

lemma a_l_coset_def':
  fixes G (structure)
  shows "a <+ H \<equiv> \<Union>h\<in>H. {a \<oplus> h}"
  unfolding a_l_coset_defs by simp

lemmas A_RCOSETS_defs =
  A_RCOSETS_def RCOSETS_def

lemma A_RCOSETS_def':
  fixes G (structure)
  shows "a_rcosets H \<equiv> \<Union>a\<in>carrier G. {H +> a}"
  unfolding A_RCOSETS_defs by (fold a_r_coset_def, simp)

lemmas set_add_defs =
  set_add_def set_mult_def

lemma set_add_def':
  fixes G (structure)
  shows "H <+> K \<equiv> \<Union>h\<in>H. \<Union>k\<in>K. {h \<oplus> k}"
  unfolding set_add_defs by simp

lemmas A_SET_INV_defs =
  A_SET_INV_def SET_INV_def

lemma A_SET_INV_def':
  fixes G (structure)
  shows "a_set_inv H \<equiv> \<Union>h\<in>H. {\<ominus> h}"
  unfolding A_SET_INV_defs by (fold a_inv_def)


subsubsection \<open>Cosets\<close>

sublocale abelian_group <
        add: group "(add_monoid G)"
  rewrites "carrier (add_monoid G) =   carrier G"
       and "   mult (add_monoid G) =       add G"
       and "    one (add_monoid G) =      zero G"
       and "  m_inv (add_monoid G) =     a_inv G"
       and "finprod (add_monoid G) =    finsum G"
       and "r_coset (add_monoid G) = a_r_coset G"
       and "l_coset (add_monoid G) = a_l_coset G"
       and "(\<lambda>a k. pow (add_monoid G) a k) = (\<lambda>a k. add_pow G k a)"
  by (rule a_group)
     (auto simp: m_inv_def a_inv_def finsum_def a_r_coset_def a_l_coset_def add_pow_def)

context abelian_group
begin

thm add.coset_mult_assoc
lemmas a_repr_independence' = add.repr_independence

(*
lemmas a_coset_add_assoc = add.coset_mult_assoc
lemmas a_coset_add_zero [simp] = add.coset_mult_one
lemmas a_coset_add_inv1 = add.coset_mult_inv1
lemmas a_coset_add_inv2 = add.coset_mult_inv2
lemmas a_coset_join1 = add.coset_join1
lemmas a_coset_join2 = add.coset_join2
lemmas a_solve_equation = add.solve_equation
lemmas a_repr_independence = add.repr_independence
lemmas a_rcosI = add.rcosI
lemmas a_rcosetsI = add.rcosetsI
*)

end

lemma (in abelian_group) a_coset_add_assoc:
     "[| M \<subseteq> carrier G; g \<in> carrier G; h \<in> carrier G |]
      ==> (M +> g) +> h = M +> (g \<oplus> h)"
by (rule group.coset_mult_assoc [OF a_group,
    folded a_r_coset_def, simplified monoid_record_simps])

thm abelian_group.a_coset_add_assoc

lemma (in abelian_group) a_coset_add_zero [simp]:
  "M \<subseteq> carrier G ==> M +> \<zero> = M"
by (rule group.coset_mult_one [OF a_group,
    folded a_r_coset_def, simplified monoid_record_simps])

lemma (in abelian_group) a_coset_add_inv1:
     "[| M +> (x \<oplus> (\<ominus> y)) = M;  x \<in> carrier G ; y \<in> carrier G;
         M \<subseteq> carrier G |] ==> M +> x = M +> y"
by (rule group.coset_mult_inv1 [OF a_group,
    folded a_r_coset_def a_inv_def, simplified monoid_record_simps])

lemma (in abelian_group) a_coset_add_inv2:
     "[| M +> x = M +> y;  x \<in> carrier G;  y \<in> carrier G;  M \<subseteq> carrier G |]
      ==> M +> (x \<oplus> (\<ominus> y)) = M"
by (rule group.coset_mult_inv2 [OF a_group,
    folded a_r_coset_def a_inv_def, simplified monoid_record_simps])

lemma (in abelian_group) a_coset_join1:
     "[| H +> x = H;  x \<in> carrier G;  subgroup H (add_monoid G) |] ==> x \<in> H"
by (rule group.coset_join1 [OF a_group,
    folded a_r_coset_def, simplified monoid_record_simps])

lemma (in abelian_group) a_solve_equation:
    "\<lbrakk>subgroup H (add_monoid G); x \<in> H; y \<in> H\<rbrakk> \<Longrightarrow> \<exists>h\<in>H. y = h \<oplus> x"
by (rule group.solve_equation [OF a_group,
    folded a_r_coset_def, simplified monoid_record_simps])

lemma (in abelian_group) a_repr_independence:
  "\<lbrakk> y \<in> H +> x; x \<in> carrier G; subgroup H (add_monoid G) \<rbrakk> \<Longrightarrow>
     H +> x = H +> y"
  using a_repr_independence' by (simp add: a_r_coset_def)

lemma (in abelian_group) a_coset_join2:
     "\<lbrakk>x \<in> carrier G;  subgroup H (add_monoid G); x\<in>H\<rbrakk> \<Longrightarrow> H +> x = H"
by (rule group.coset_join2 [OF a_group,
    folded a_r_coset_def, simplified monoid_record_simps])

lemma (in abelian_monoid) a_r_coset_subset_G:
     "[| H \<subseteq> carrier G; x \<in> carrier G |] ==> H +> x \<subseteq> carrier G"
by (rule monoid.r_coset_subset_G [OF a_monoid,
    folded a_r_coset_def, simplified monoid_record_simps])

lemma (in abelian_group) a_rcosI:
     "[| h \<in> H; H \<subseteq> carrier G; x \<in> carrier G|] ==> h \<oplus> x \<in> H +> x"
by (rule group.rcosI [OF a_group,
    folded a_r_coset_def, simplified monoid_record_simps])

lemma (in abelian_group) a_rcosetsI:
     "\<lbrakk>H \<subseteq> carrier G; x \<in> carrier G\<rbrakk> \<Longrightarrow> H +> x \<in> a_rcosets H"
by (rule group.rcosetsI [OF a_group,
    folded a_r_coset_def A_RCOSETS_def, simplified monoid_record_simps])

text\<open>Really needed?\<close>
lemma (in abelian_group) a_transpose_inv:
     "[| x \<oplus> y = z;  x \<in> carrier G;  y \<in> carrier G;  z \<in> carrier G |]
      ==> (\<ominus> x) \<oplus> z = y"
  using r_neg1 by blast



subsubsection \<open>Subgroups\<close>

locale additive_subgroup =
  fixes H and G (structure)
  assumes a_subgroup: "subgroup H (add_monoid G)"

lemma (in additive_subgroup) is_additive_subgroup:
  shows "additive_subgroup H G"
by (rule additive_subgroup_axioms)

lemma additive_subgroupI:
  fixes G (structure)
  assumes a_subgroup: "subgroup H (add_monoid G)"
  shows "additive_subgroup H G"
by (rule additive_subgroup.intro) (rule a_subgroup)

lemma (in additive_subgroup) a_subset:
     "H \<subseteq> carrier G"
by (rule subgroup.subset[OF a_subgroup,
    simplified monoid_record_simps])

lemma (in additive_subgroup) a_closed [intro, simp]:
     "\<lbrakk>x \<in> H; y \<in> H\<rbrakk> \<Longrightarrow> x \<oplus> y \<in> H"
by (rule subgroup.m_closed[OF a_subgroup,
    simplified monoid_record_simps])

lemma (in additive_subgroup) zero_closed [simp]:
     "\<zero> \<in> H"
by (rule subgroup.one_closed[OF a_subgroup,
    simplified monoid_record_simps])

lemma (in additive_subgroup) a_inv_closed [intro,simp]:
     "x \<in> H \<Longrightarrow> \<ominus> x \<in> H"
by (rule subgroup.m_inv_closed[OF a_subgroup,
    folded a_inv_def, simplified monoid_record_simps])


subsubsection \<open>Additive subgroups are normal\<close>

text \<open>Every subgroup of an \<open>abelian_group\<close> is normal\<close>

locale abelian_subgroup = additive_subgroup + abelian_group G +
  assumes a_normal: "normal H (add_monoid G)"

lemma (in abelian_subgroup) is_abelian_subgroup:
  shows "abelian_subgroup H G"
by (rule abelian_subgroup_axioms)

lemma abelian_subgroupI:
  assumes a_normal: "normal H (add_monoid G)"
      and a_comm: "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<oplus>\<^bsub>G\<^esub> y = y \<oplus>\<^bsub>G\<^esub> x"
  shows "abelian_subgroup H G"
proof -
  interpret normal "H" "(add_monoid G)"
    by (rule a_normal)

  show "abelian_subgroup H G"
    by standard (simp add: a_comm)
qed

lemma abelian_subgroupI2:
  fixes G (structure)
  assumes a_comm_group: "comm_group (add_monoid G)"
      and a_subgroup: "subgroup H (add_monoid G)"
  shows "abelian_subgroup H G"
proof -
  interpret comm_group "(add_monoid G)"
    by (rule a_comm_group)
  interpret subgroup "H" "(add_monoid G)"
    by (rule a_subgroup)
  have "(\<Union>xa\<in>H. {xa \<oplus> x}) = (\<Union>xa\<in>H. {x \<oplus> xa})" if "x \<in> carrier G" for x
  proof -
    have "H \<subseteq> carrier G"
      using a_subgroup that unfolding subgroup_def by simp
    with that show "(\<Union>h\<in>H. {h \<oplus>\<^bsub>G\<^esub> x}) = (\<Union>h\<in>H. {x \<oplus>\<^bsub>G\<^esub> h})"
      using m_comm [simplified] by fastforce
  qed
  then show "abelian_subgroup H G"
    by unfold_locales (auto simp: r_coset_def l_coset_def)
qed

lemma abelian_subgroupI3:
  fixes G (structure)
  assumes "additive_subgroup H G"
    and "abelian_group G"
  shows "abelian_subgroup H G"
  using assms abelian_subgroupI2 abelian_group.a_comm_group additive_subgroup_def by blast

lemma (in abelian_subgroup) a_coset_eq:
     "(\<forall>x \<in> carrier G. H +> x = x <+ H)"
by (rule normal.coset_eq[OF a_normal,
    folded a_r_coset_def a_l_coset_def, simplified monoid_record_simps])

lemma (in abelian_subgroup) a_inv_op_closed1:
  shows "\<lbrakk>x \<in> carrier G; h \<in> H\<rbrakk> \<Longrightarrow> (\<ominus> x) \<oplus> h \<oplus> x \<in> H"
by (rule normal.inv_op_closed1 [OF a_normal,
    folded a_inv_def, simplified monoid_record_simps])

lemma (in abelian_subgroup) a_inv_op_closed2:
  shows "\<lbrakk>x \<in> carrier G; h \<in> H\<rbrakk> \<Longrightarrow> x \<oplus> h \<oplus> (\<ominus> x) \<in> H"
by (rule normal.inv_op_closed2 [OF a_normal,
    folded a_inv_def, simplified monoid_record_simps])

lemma (in abelian_group) a_lcos_m_assoc:
  "\<lbrakk> M \<subseteq> carrier G; g \<in> carrier G; h \<in> carrier G \<rbrakk> \<Longrightarrow> g <+ (h <+ M) = (g \<oplus> h) <+ M"
by (rule group.lcos_m_assoc [OF a_group,
    folded a_l_coset_def, simplified monoid_record_simps])

lemma (in abelian_group) a_lcos_mult_one:
     "M \<subseteq> carrier G ==> \<zero> <+ M = M"
by (rule group.lcos_mult_one [OF a_group,
    folded a_l_coset_def, simplified monoid_record_simps])

lemma (in abelian_group) a_l_coset_subset_G:
  "\<lbrakk> H \<subseteq> carrier G; x \<in> carrier G \<rbrakk> \<Longrightarrow> x <+ H \<subseteq> carrier G"
by (rule group.l_coset_subset_G [OF a_group,
    folded a_l_coset_def, simplified monoid_record_simps])

lemma (in abelian_group) a_l_coset_swap:
     "\<lbrakk>y \<in> x <+ H;  x \<in> carrier G;  subgroup H (add_monoid G)\<rbrakk> \<Longrightarrow> x \<in> y <+ H"
by (rule group.l_coset_swap [OF a_group,
    folded a_l_coset_def, simplified monoid_record_simps])

lemma (in abelian_group) a_l_coset_carrier:
     "[| y \<in> x <+ H;  x \<in> carrier G;  subgroup H (add_monoid G) |] ==> y \<in> carrier G"
by (rule group.l_coset_carrier [OF a_group,
    folded a_l_coset_def, simplified monoid_record_simps])

lemma (in abelian_group) a_l_repr_imp_subset:
  assumes "y \<in> x <+ H" "x \<in> carrier G" "subgroup H (add_monoid G)"
  shows "y <+ H \<subseteq> x <+ H"
  by (metis (full_types) a_l_coset_defs(1) add.l_repr_independence assms set_eq_subset)

lemma (in abelian_group) a_l_repr_independence:
  assumes y: "y \<in> x <+ H" and x: "x \<in> carrier G" and sb: "subgroup H (add_monoid G)"
  shows "x <+ H = y <+ H"
apply (rule group.l_repr_independence [OF a_group,
    folded a_l_coset_def, simplified monoid_record_simps])
apply (rule y)
apply (rule x)
apply (rule sb)
done

lemma (in abelian_group) setadd_subset_G:
     "\<lbrakk>H \<subseteq> carrier G; K \<subseteq> carrier G\<rbrakk> \<Longrightarrow> H <+> K \<subseteq> carrier G"
by (rule group.setmult_subset_G [OF a_group,
    folded set_add_def, simplified monoid_record_simps])

lemma (in abelian_group) subgroup_add_id: "subgroup H (add_monoid G) \<Longrightarrow> H <+> H = H"
by (rule group.subgroup_mult_id [OF a_group,
    folded set_add_def, simplified monoid_record_simps])

lemma (in abelian_subgroup) a_rcos_inv:
  assumes x:     "x \<in> carrier G"
  shows "a_set_inv (H +> x) = H +> (\<ominus> x)" 
by (rule normal.rcos_inv [OF a_normal,
  folded a_r_coset_def a_inv_def A_SET_INV_def, simplified monoid_record_simps]) (rule x)

lemma (in abelian_group) a_setmult_rcos_assoc:
     "\<lbrakk>H \<subseteq> carrier G; K \<subseteq> carrier G; x \<in> carrier G\<rbrakk>
      \<Longrightarrow> H <+> (K +> x) = (H <+> K) +> x"
by (rule group.setmult_rcos_assoc [OF a_group,
    folded set_add_def a_r_coset_def, simplified monoid_record_simps])

lemma (in abelian_group) a_rcos_assoc_lcos:
     "\<lbrakk>H \<subseteq> carrier G; K \<subseteq> carrier G; x \<in> carrier G\<rbrakk>
      \<Longrightarrow> (H +> x) <+> K = H <+> (x <+ K)"
by (rule group.rcos_assoc_lcos [OF a_group,
     folded set_add_def a_r_coset_def a_l_coset_def, simplified monoid_record_simps])

lemma (in abelian_subgroup) a_rcos_sum:
     "\<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk>
      \<Longrightarrow> (H +> x) <+> (H +> y) = H +> (x \<oplus> y)"
by (rule normal.rcos_sum [OF a_normal,
    folded set_add_def a_r_coset_def, simplified monoid_record_simps])

lemma (in abelian_subgroup) rcosets_add_eq:
  "M \<in> a_rcosets H \<Longrightarrow> H <+> M = M"
  \<comment> \<open>generalizes \<open>subgroup_mult_id\<close>\<close>
by (rule normal.rcosets_mult_eq [OF a_normal,
    folded set_add_def A_RCOSETS_def, simplified monoid_record_simps])


subsubsection \<open>Congruence Relation\<close>

lemma (in abelian_subgroup) a_equiv_rcong:
   shows "equiv (carrier G) (racong H)"
by (rule subgroup.equiv_rcong [OF a_subgroup a_group,
    folded a_r_congruent_def, simplified monoid_record_simps])

lemma (in abelian_subgroup) a_l_coset_eq_rcong:
  assumes a: "a \<in> carrier G"
  shows "a <+ H = racong H `` {a}"
by (rule subgroup.l_coset_eq_rcong [OF a_subgroup a_group,
    folded a_r_congruent_def a_l_coset_def, simplified monoid_record_simps]) (rule a)

lemma (in abelian_subgroup) a_rcos_equation:
  shows
     "\<lbrakk>ha \<oplus> a = h \<oplus> b; a \<in> carrier G;  b \<in> carrier G;  
        h \<in> H;  ha \<in> H;  hb \<in> H\<rbrakk>
      \<Longrightarrow> hb \<oplus> a \<in> (\<Union>h\<in>H. {h \<oplus> b})"
by (rule group.rcos_equation [OF a_group a_subgroup,
    folded a_r_congruent_def a_l_coset_def, simplified monoid_record_simps])

lemma (in abelian_subgroup) a_rcos_disjoint: "pairwise disjnt (a_rcosets H)"
by (rule group.rcos_disjoint [OF a_group a_subgroup,
    folded A_RCOSETS_def, simplified monoid_record_simps])

lemma (in abelian_subgroup) a_rcos_self:
  shows "x \<in> carrier G \<Longrightarrow> x \<in> H +> x"
by (rule group.rcos_self [OF a_group _ a_subgroup,
    folded a_r_coset_def, simplified monoid_record_simps])

lemma (in abelian_subgroup) a_rcosets_part_G:
  shows "\<Union>(a_rcosets H) = carrier G"
by (rule group.rcosets_part_G [OF a_group a_subgroup,
    folded A_RCOSETS_def, simplified monoid_record_simps])

lemma (in abelian_subgroup) a_cosets_finite:
     "\<lbrakk>c \<in> a_rcosets H;  H \<subseteq> carrier G;  finite (carrier G)\<rbrakk> \<Longrightarrow> finite c"
by (rule group.cosets_finite [OF a_group,
    folded A_RCOSETS_def, simplified monoid_record_simps])

lemma (in abelian_group) a_card_cosets_equal:
     "\<lbrakk>c \<in> a_rcosets H;  H \<subseteq> carrier G; finite(carrier G)\<rbrakk>
      \<Longrightarrow> card c = card H"
  by (simp add: A_RCOSETS_defs(1) add.card_rcosets_equal)

lemma (in abelian_group) rcosets_subset_PowG:
     "additive_subgroup H G  \<Longrightarrow> a_rcosets H \<subseteq> Pow(carrier G)"
by (rule group.rcosets_subset_PowG [OF a_group,
    folded A_RCOSETS_def, simplified monoid_record_simps],
    rule additive_subgroup.a_subgroup)

theorem (in abelian_group) a_lagrange:
     "\<lbrakk>finite(carrier G); additive_subgroup H G\<rbrakk>
      \<Longrightarrow> card(a_rcosets H) * card(H) = order(G)"
by (rule group.lagrange [OF a_group,
    folded A_RCOSETS_def, simplified monoid_record_simps order_def, folded order_def])
    (fast intro!: additive_subgroup.a_subgroup)+


subsubsection \<open>Factorization\<close>

lemmas A_FactGroup_defs = A_FactGroup_def FactGroup_def

lemma A_FactGroup_def':
  fixes G (structure)
  shows "G A_Mod H \<equiv> \<lparr>carrier = a_rcosets\<^bsub>G\<^esub> H, mult = set_add G, one = H\<rparr>"
unfolding A_FactGroup_defs
by (fold A_RCOSETS_def set_add_def)


lemma (in abelian_subgroup) a_setmult_closed:
     "\<lbrakk>K1 \<in> a_rcosets H; K2 \<in> a_rcosets H\<rbrakk> \<Longrightarrow> K1 <+> K2 \<in> a_rcosets H"
by (rule normal.setmult_closed [OF a_normal,
    folded A_RCOSETS_def set_add_def, simplified monoid_record_simps])

lemma (in abelian_subgroup) a_setinv_closed:
     "K \<in> a_rcosets H \<Longrightarrow> a_set_inv K \<in> a_rcosets H"
by (rule normal.setinv_closed [OF a_normal,
    folded A_RCOSETS_def A_SET_INV_def, simplified monoid_record_simps])

lemma (in abelian_subgroup) a_rcosets_assoc:
     "\<lbrakk>M1 \<in> a_rcosets H; M2 \<in> a_rcosets H; M3 \<in> a_rcosets H\<rbrakk>
      \<Longrightarrow> M1 <+> M2 <+> M3 = M1 <+> (M2 <+> M3)"
by (rule normal.rcosets_assoc [OF a_normal,
    folded A_RCOSETS_def set_add_def, simplified monoid_record_simps])

lemma (in abelian_subgroup) a_subgroup_in_rcosets:
     "H \<in> a_rcosets H"
by (rule subgroup.subgroup_in_rcosets [OF a_subgroup a_group,
    folded A_RCOSETS_def, simplified monoid_record_simps])

lemma (in abelian_subgroup) a_rcosets_inv_mult_group_eq:
     "M \<in> a_rcosets H \<Longrightarrow> a_set_inv M <+> M = H"
by (rule normal.rcosets_inv_mult_group_eq [OF a_normal,
    folded A_RCOSETS_def A_SET_INV_def set_add_def, simplified monoid_record_simps])

theorem (in abelian_subgroup) a_factorgroup_is_group:
  "group (G A_Mod H)"
by (rule normal.factorgroup_is_group [OF a_normal,
    folded A_FactGroup_def, simplified monoid_record_simps])

text \<open>Since the Factorization is based on an \emph{abelian} subgroup, is results in 
        a commutative group\<close>
theorem (in abelian_subgroup) a_factorgroup_is_comm_group: "comm_group (G A_Mod H)"
proof -
  have "Group.comm_monoid_axioms (G A_Mod H)"
    apply (rule comm_monoid_axioms.intro)
    apply (auto simp: A_FactGroup_def FactGroup_def RCOSETS_def a_normal add.m_comm normal.rcos_sum)
    done
  then show ?thesis
    by (intro comm_group.intro comm_monoid.intro) (simp_all add: a_factorgroup_is_group group.is_monoid)
qed

lemma add_A_FactGroup [simp]: "X \<otimes>\<^bsub>(G A_Mod H)\<^esub> X' = X <+>\<^bsub>G\<^esub> X'"
by (simp add: A_FactGroup_def set_add_def)

lemma (in abelian_subgroup) a_inv_FactGroup:
     "X \<in> carrier (G A_Mod H) \<Longrightarrow> inv\<^bsub>G A_Mod H\<^esub> X = a_set_inv X"
by (rule normal.inv_FactGroup [OF a_normal,
    folded A_FactGroup_def A_SET_INV_def, simplified monoid_record_simps])

text\<open>The coset map is a homomorphism from \<^term>\<open>G\<close> to the quotient group
  \<^term>\<open>G Mod H\<close>\<close>
lemma (in abelian_subgroup) a_r_coset_hom_A_Mod:
  "(\<lambda>a. H +> a) \<in> hom (add_monoid G) (G A_Mod H)"
by (rule normal.r_coset_hom_Mod [OF a_normal,
    folded A_FactGroup_def a_r_coset_def, simplified monoid_record_simps])

text \<open>The isomorphism theorems have been omitted from lifting, at
  least for now\<close>


subsubsection\<open>The First Isomorphism Theorem\<close>

text\<open>The quotient by the kernel of a homomorphism is isomorphic to the 
  range of that homomorphism.\<close>

lemmas a_kernel_defs =
  a_kernel_def kernel_def

lemma a_kernel_def':
  "a_kernel R S h = {x \<in> carrier R. h x = \<zero>\<^bsub>S\<^esub>}"
by (rule a_kernel_def[unfolded kernel_def, simplified ring_record_simps])


subsubsection \<open>Homomorphisms\<close>

lemma abelian_group_homI:
  assumes "abelian_group G"
  assumes "abelian_group H"
  assumes a_group_hom: "group_hom (add_monoid G)
                                  (add_monoid H) h"
  shows "abelian_group_hom G H h"
proof -
  interpret G: abelian_group G by fact
  interpret H: abelian_group H by fact
  show ?thesis
    by (intro abelian_group_hom.intro abelian_group_hom_axioms.intro 
        G.abelian_group_axioms H.abelian_group_axioms a_group_hom)
qed

lemma (in abelian_group_hom) is_abelian_group_hom:
  "abelian_group_hom G H h"
  ..

lemma (in abelian_group_hom) hom_add [simp]:
  "[| x \<in> carrier G; y \<in> carrier G |]
        ==> h (x \<oplus>\<^bsub>G\<^esub> y) = h x \<oplus>\<^bsub>H\<^esub> h y"
by (rule group_hom.hom_mult[OF a_group_hom,
    simplified ring_record_simps])

lemma (in abelian_group_hom) hom_closed [simp]:
  "x \<in> carrier G \<Longrightarrow> h x \<in> carrier H"
by (rule group_hom.hom_closed[OF a_group_hom,
    simplified ring_record_simps])

lemma (in abelian_group_hom) zero_closed [simp]:
  "h \<zero> \<in> carrier H"
  by simp

lemma (in abelian_group_hom) hom_zero [simp]:
  "h \<zero> = \<zero>\<^bsub>H\<^esub>"
by (rule group_hom.hom_one[OF a_group_hom,
    simplified ring_record_simps])

lemma (in abelian_group_hom) a_inv_closed [simp]:
  "x \<in> carrier G ==> h (\<ominus>x) \<in> carrier H"
  by simp

lemma (in abelian_group_hom) hom_a_inv [simp]:
  "x \<in> carrier G ==> h (\<ominus>x) = \<ominus>\<^bsub>H\<^esub> (h x)"
by (rule group_hom.hom_inv[OF a_group_hom,
    folded a_inv_def, simplified ring_record_simps])

lemma (in abelian_group_hom) additive_subgroup_a_kernel:
  "additive_subgroup (a_kernel G H h) G"
  by (simp add: additive_subgroup.intro a_group_hom a_kernel_def group_hom.subgroup_kernel)

text\<open>The kernel of a homomorphism is an abelian subgroup\<close>
lemma (in abelian_group_hom) abelian_subgroup_a_kernel:
  "abelian_subgroup (a_kernel G H h) G"
  apply (rule abelian_subgroupI)
   apply (simp add: G.abelian_group_axioms abelian_subgroup.a_normal abelian_subgroupI3 additive_subgroup_a_kernel)
  apply (simp add: G.a_comm)
  done

lemma (in abelian_group_hom) A_FactGroup_nonempty:
  assumes X: "X \<in> carrier (G A_Mod a_kernel G H h)"
  shows "X \<noteq> {}"
by (rule group_hom.FactGroup_nonempty[OF a_group_hom,
    folded a_kernel_def A_FactGroup_def, simplified ring_record_simps]) (rule X)

lemma (in abelian_group_hom) FactGroup_the_elem_mem:
  assumes X: "X \<in> carrier (G A_Mod (a_kernel G H h))"
  shows "the_elem (h`X) \<in> carrier H"
by (rule group_hom.FactGroup_the_elem_mem[OF a_group_hom,
    folded a_kernel_def A_FactGroup_def, simplified ring_record_simps]) (rule X)

lemma (in abelian_group_hom) A_FactGroup_hom:
     "(\<lambda>X. the_elem (h`X)) \<in> hom (G A_Mod (a_kernel G H h))
          (add_monoid H)"
by (rule group_hom.FactGroup_hom[OF a_group_hom,
    folded a_kernel_def A_FactGroup_def, simplified ring_record_simps])

lemma (in abelian_group_hom) A_FactGroup_inj_on:
     "inj_on (\<lambda>X. the_elem (h ` X)) (carrier (G A_Mod a_kernel G H h))"
by (rule group_hom.FactGroup_inj_on[OF a_group_hom,
    folded a_kernel_def A_FactGroup_def, simplified ring_record_simps])

text\<open>If the homomorphism \<^term>\<open>h\<close> is onto \<^term>\<open>H\<close>, then so is the
homomorphism from the quotient group\<close>
lemma (in abelian_group_hom) A_FactGroup_onto:
  assumes h: "h ` carrier G = carrier H"
  shows "(\<lambda>X. the_elem (h ` X)) ` carrier (G A_Mod a_kernel G H h) = carrier H"
by (rule group_hom.FactGroup_onto[OF a_group_hom,
    folded a_kernel_def A_FactGroup_def, simplified ring_record_simps]) (rule h)

text\<open>If \<^term>\<open>h\<close> is a homomorphism from \<^term>\<open>G\<close> onto \<^term>\<open>H\<close>, then the
 quotient group \<^term>\<open>G Mod (kernel G H h)\<close> is isomorphic to \<^term>\<open>H\<close>.\<close>
theorem (in abelian_group_hom) A_FactGroup_iso_set:
  "h ` carrier G = carrier H
   \<Longrightarrow> (\<lambda>X. the_elem (h`X)) \<in> iso (G A_Mod (a_kernel G H h)) (add_monoid H)"
by (rule group_hom.FactGroup_iso_set[OF a_group_hom,
    folded a_kernel_def A_FactGroup_def, simplified ring_record_simps])

corollary (in abelian_group_hom) A_FactGroup_iso :
  "h ` carrier G = carrier H
   \<Longrightarrow>  (G A_Mod (a_kernel G H h)) \<cong>  (add_monoid H)"
  using A_FactGroup_iso_set unfolding is_iso_def by auto

subsubsection \<open>Cosets\<close>

text \<open>Not eveything from \texttt{CosetExt.thy} is lifted here.\<close>

lemma (in additive_subgroup) a_Hcarr [simp]:
  assumes hH: "h \<in> H"
  shows "h \<in> carrier G"
by (rule subgroup.mem_carrier [OF a_subgroup,
    simplified monoid_record_simps]) (rule hH)


lemma (in abelian_subgroup) a_elemrcos_carrier:
  assumes acarr: "a \<in> carrier G"
      and a': "a' \<in> H +> a"
  shows "a' \<in> carrier G"
by (rule subgroup.elemrcos_carrier [OF a_subgroup a_group,
    folded a_r_coset_def, simplified monoid_record_simps]) (rule acarr, rule a')

lemma (in abelian_subgroup) a_rcos_const:
  assumes hH: "h \<in> H"
  shows "H +> h = H"
by (rule subgroup.rcos_const [OF a_subgroup a_group,
    folded a_r_coset_def, simplified monoid_record_simps]) (rule hH)

lemma (in abelian_subgroup) a_rcos_module_imp:
  assumes xcarr: "x \<in> carrier G"
      and x'cos: "x' \<in> H +> x"
  shows "(x' \<oplus> \<ominus>x) \<in> H"
by (rule subgroup.rcos_module_imp [OF a_subgroup a_group,
    folded a_r_coset_def a_inv_def, simplified monoid_record_simps]) (rule xcarr, rule x'cos)

lemma (in abelian_subgroup) a_rcos_module_rev:
  assumes "x \<in> carrier G" "x' \<in> carrier G"
      and "(x' \<oplus> \<ominus>x) \<in> H"
  shows "x' \<in> H +> x"
using assms
by (rule subgroup.rcos_module_rev [OF a_subgroup a_group,
    folded a_r_coset_def a_inv_def, simplified monoid_record_simps])

lemma (in abelian_subgroup) a_rcos_module:
  assumes "x \<in> carrier G" "x' \<in> carrier G"
  shows "(x' \<in> H +> x) = (x' \<oplus> \<ominus>x \<in> H)"
using assms
by (rule subgroup.rcos_module [OF a_subgroup a_group,
    folded a_r_coset_def a_inv_def, simplified monoid_record_simps])

\<comment> \<open>variant\<close>
lemma (in abelian_subgroup) a_rcos_module_minus:
  assumes "ring G"
  assumes carr: "x \<in> carrier G" "x' \<in> carrier G"
  shows "(x' \<in> H +> x) = (x' \<ominus> x \<in> H)"
proof -
  interpret G: ring G by fact
  from carr
  have "(x' \<in> H +> x) = (x' \<oplus> \<ominus>x \<in> H)" by (rule a_rcos_module)
  with carr
  show "(x' \<in> H +> x) = (x' \<ominus> x \<in> H)"
    by (simp add: minus_eq)
qed

lemma (in abelian_subgroup) a_repr_independence':
  assumes "y \<in> H +> x" "x \<in> carrier G"
  shows "H +> x = H +> y"
  using a_repr_independence a_subgroup assms by blast

lemma (in abelian_subgroup) a_repr_independenceD:
  assumes "y \<in> carrier G" "H +> x = H +> y"
  shows "y \<in> H +> x"
  by (simp add: a_rcos_self assms)


lemma (in abelian_subgroup) a_rcosets_carrier:
  "X \<in> a_rcosets H \<Longrightarrow> X \<subseteq> carrier G"
  using a_rcosets_part_G by auto


subsubsection \<open>Addition of Subgroups\<close>

lemma (in abelian_monoid) set_add_closed:
  assumes "A \<subseteq> carrier G" "B \<subseteq> carrier G"
  shows "A <+> B \<subseteq> carrier G"
  by (simp add: assms add.set_mult_closed set_add_defs(1))

lemma (in abelian_group) add_additive_subgroups:
  assumes subH: "additive_subgroup H G"
    and subK: "additive_subgroup K G"
  shows "additive_subgroup (H <+> K) G"
  unfolding set_add_def
  using add.mult_subgroups additive_subgroup_def subH subK
  by (blast intro: additive_subgroup.intro)

end
