(*  Title:      HOL/Algebra/Coset.thy
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
*)

header{*Cosets and Quotient Groups*}

theory Coset = Group + Exponent:

declare (in group) l_inv [simp] and r_inv [simp]

constdefs (structure G)
  r_coset    :: "[_, 'a set, 'a] => 'a set"    (infixl "#>\<index>" 60)
  "H #> a == (% x. x \<otimes> a) ` H"

  l_coset    :: "[_, 'a, 'a set] => 'a set"    (infixl "<#\<index>" 60)
  "a <# H == (% x. a \<otimes> x) ` H"

  rcosets  :: "[_, 'a set] => ('a set)set"
  "rcosets G H == r_coset G H ` (carrier G)"

  set_mult  :: "[_, 'a set ,'a set] => 'a set" (infixl "<#>\<index>" 60)
  "H <#> K == (%(x,y). x \<otimes> y) ` (H \<times> K)"

  set_inv   :: "[_,'a set] => 'a set"
  "set_inv G H == m_inv G ` H"

  normal     :: "['a set, _] => bool"       (infixl "<|" 60)
  "normal H G == subgroup H G &
                  (\<forall>x \<in> carrier G. r_coset G H x = l_coset G x H)"

syntax (xsymbols)
  normal :: "['a set, ('a,'b) monoid_scheme] => bool"  (infixl "\<lhd>" 60)


subsection {*Basic Properties of Cosets*}

lemma (in group) r_coset_eq: "H #> a = {b . \<exists>h\<in>H. h \<otimes> a = b}"
by (auto simp add: r_coset_def)

lemma (in group) l_coset_eq: "a <# H = {b . \<exists>h\<in>H. a \<otimes> h = b}"
by (auto simp add: l_coset_def)

lemma (in group) setrcos_eq: "rcosets G H = {C . \<exists>a\<in>carrier G. C = H #> a}"
by (auto simp add: rcosets_def)

lemma (in group) set_mult_eq: "H <#> K = {c . \<exists>h\<in>H. \<exists>k\<in>K. c = h \<otimes> k}"
by (simp add: set_mult_def image_def)

lemma (in group) coset_mult_assoc:
     "[| M \<subseteq> carrier G; g \<in> carrier G; h \<in> carrier G |]
      ==> (M #> g) #> h = M #> (g \<otimes> h)"
by (force simp add: r_coset_def m_assoc)

lemma (in group) coset_mult_one [simp]: "M \<subseteq> carrier G ==> M #> \<one> = M"
by (force simp add: r_coset_def)

lemma (in group) coset_mult_inv1:
     "[| M #> (x \<otimes> (inv y)) = M;  x \<in> carrier G ; y \<in> carrier G;
         M \<subseteq> carrier G |] ==> M #> x = M #> y"
apply (erule subst [of concl: "%z. M #> x = z #> y"])
apply (simp add: coset_mult_assoc m_assoc)
done

lemma (in group) coset_mult_inv2:
     "[| M #> x = M #> y;  x \<in> carrier G;  y \<in> carrier G;  M \<subseteq> carrier G |]
      ==> M #> (x \<otimes> (inv y)) = M "
apply (simp add: coset_mult_assoc [symmetric])
apply (simp add: coset_mult_assoc)
done

lemma (in group) coset_join1:
     "[| H #> x = H;  x \<in> carrier G;  subgroup H G |] ==> x \<in> H"
apply (erule subst)
apply (simp add: r_coset_eq)
apply (blast intro: l_one subgroup.one_closed)
done

lemma (in group) solve_equation:
    "\<lbrakk>subgroup H G; x \<in> H; y \<in> H\<rbrakk> \<Longrightarrow> \<exists>h\<in>H. h \<otimes> x = y"
apply (rule bexI [of _ "y \<otimes> (inv x)"])
apply (auto simp add: subgroup.m_closed subgroup.m_inv_closed m_assoc
                      subgroup.subset [THEN subsetD])
done

lemma (in group) coset_join2:
     "[| x \<in> carrier G;  subgroup H G;  x\<in>H |] ==> H #> x = H"
by (force simp add: subgroup.m_closed r_coset_eq solve_equation)

lemma (in group) r_coset_subset_G:
     "[| H \<subseteq> carrier G; x \<in> carrier G |] ==> H #> x \<subseteq> carrier G"
by (auto simp add: r_coset_def)

lemma (in group) rcosI:
     "[| h \<in> H; H \<subseteq> carrier G; x \<in> carrier G|] ==> h \<otimes> x \<in> H #> x"
by (auto simp add: r_coset_def)

lemma (in group) setrcosI:
     "[| H \<subseteq> carrier G; x \<in> carrier G |] ==> H #> x \<in> rcosets G H"
by (auto simp add: setrcos_eq)


text{*Really needed?*}
lemma (in group) transpose_inv:
     "[| x \<otimes> y = z;  x \<in> carrier G;  y \<in> carrier G;  z \<in> carrier G |]
      ==> (inv x) \<otimes> z = y"
by (force simp add: m_assoc [symmetric])

lemma (in group) repr_independence:
     "[| y \<in> H #> x;  x \<in> carrier G; subgroup H G |] ==> H #> x = H #> y"
by (auto simp add: r_coset_eq m_assoc [symmetric]
                   subgroup.subset [THEN subsetD]
                   subgroup.m_closed solve_equation)

lemma (in group) rcos_self: "[| x \<in> carrier G; subgroup H G |] ==> x \<in> H #> x"
apply (simp add: r_coset_eq)
apply (blast intro: l_one subgroup.subset [THEN subsetD]
                    subgroup.one_closed)
done


subsection {* Normal subgroups *}

lemma normal_imp_subgroup: "H <| G ==> subgroup H G"
by (simp add: normal_def)

lemma (in group) normal_inv_op_closed1:
     "\<lbrakk>H \<lhd> G; x \<in> carrier G; h \<in> H\<rbrakk> \<Longrightarrow> (inv x) \<otimes> h \<otimes> x \<in> H"
apply (auto simp add: l_coset_def r_coset_def normal_def)
apply (drule bspec, assumption)
apply (drule equalityD1 [THEN subsetD], blast, clarify)
apply (simp add: m_assoc subgroup.subset [THEN subsetD])
apply (simp add: m_assoc [symmetric] subgroup.subset [THEN subsetD])
done

lemma (in group) normal_inv_op_closed2:
     "\<lbrakk>H \<lhd> G; x \<in> carrier G; h \<in> H\<rbrakk> \<Longrightarrow> x \<otimes> h \<otimes> (inv x) \<in> H"
apply (drule normal_inv_op_closed1 [of H "(inv x)"])
apply auto
done

text{*Alternative characterization of normal subgroups*}
lemma (in group) normal_inv_iff:
     "(N \<lhd> G) = 
      (subgroup N G & (\<forall>x \<in> carrier G. \<forall>h \<in> N. x \<otimes> h \<otimes> (inv x) \<in> N))"
      (is "_ = ?rhs")
proof
  assume N: "N \<lhd> G"
  show ?rhs
    by (blast intro: N normal_imp_subgroup normal_inv_op_closed2) 
next
  assume ?rhs
  hence sg: "subgroup N G" 
    and closed: "!!x. x\<in>carrier G ==> \<forall>h\<in>N. x \<otimes> h \<otimes> inv x \<in> N" by auto
  hence sb: "N \<subseteq> carrier G" by (simp add: subgroup.subset) 
  show "N \<lhd> G"
  proof (simp add: sg normal_def l_coset_def r_coset_def, clarify)
    fix x
    assume x: "x \<in> carrier G"
    show "(\<lambda>n. n \<otimes> x) ` N = op \<otimes> x ` N"
    proof
      show "(\<lambda>n. n \<otimes> x) ` N \<subseteq> op \<otimes> x ` N"
      proof clarify
        fix n
        assume n: "n \<in> N" 
        show "n \<otimes> x \<in> op \<otimes> x ` N"
        proof 
          show "n \<otimes> x = x \<otimes> (inv x \<otimes> n \<otimes> x)"
            by (simp add: x n m_assoc [symmetric] sb [THEN subsetD])
          with closed [of "inv x"]
          show "inv x \<otimes> n \<otimes> x \<in> N" by (simp add: x n)
        qed
      qed
    next
      show "op \<otimes> x ` N \<subseteq> (\<lambda>n. n \<otimes> x) ` N" 
      proof clarify
        fix n
        assume n: "n \<in> N" 
        show "x \<otimes> n \<in> (\<lambda>n. n \<otimes> x) ` N"
        proof 
          show "x \<otimes> n = (x \<otimes> n \<otimes> inv x) \<otimes> x"
            by (simp add: x n m_assoc sb [THEN subsetD])
          show "x \<otimes> n \<otimes> inv x \<in> N" by (simp add: x n closed)
        qed
      qed
    qed
  qed
qed

subsection{*More Properties of Cosets*}

lemma (in group) lcos_m_assoc:
     "[| M \<subseteq> carrier G; g \<in> carrier G; h \<in> carrier G |]
      ==> g <# (h <# M) = (g \<otimes> h) <# M"
by (force simp add: l_coset_def m_assoc)

lemma (in group) lcos_mult_one: "M \<subseteq> carrier G ==> \<one> <# M = M"
by (force simp add: l_coset_def)

lemma (in group) l_coset_subset_G:
     "[| H \<subseteq> carrier G; x \<in> carrier G |] ==> x <# H \<subseteq> carrier G"
by (auto simp add: l_coset_def subsetD)

lemma (in group) l_coset_swap:
     "[| y \<in> x <# H;  x \<in> carrier G;  subgroup H G |] ==> x \<in> y <# H"
proof (simp add: l_coset_eq)
  assume "\<exists>h\<in>H. x \<otimes> h = y"
    and x: "x \<in> carrier G"
    and sb: "subgroup H G"
  then obtain h' where h': "h' \<in> H & x \<otimes> h' = y" by blast
  show "\<exists>h\<in>H. y \<otimes> h = x"
  proof
    show "y \<otimes> inv h' = x" using h' x sb
      by (auto simp add: m_assoc subgroup.subset [THEN subsetD])
    show "inv h' \<in> H" using h' sb
      by (auto simp add: subgroup.subset [THEN subsetD] subgroup.m_inv_closed)
  qed
qed

lemma (in group) l_coset_carrier:
     "[| y \<in> x <# H;  x \<in> carrier G;  subgroup H G |] ==> y \<in> carrier G"
by (auto simp add: l_coset_def m_assoc
                   subgroup.subset [THEN subsetD] subgroup.m_closed)

lemma (in group) l_repr_imp_subset:
  assumes y: "y \<in> x <# H" and x: "x \<in> carrier G" and sb: "subgroup H G"
  shows "y <# H \<subseteq> x <# H"
proof -
  from y
  obtain h' where "h' \<in> H" "x \<otimes> h' = y" by (auto simp add: l_coset_def)
  thus ?thesis using x sb
    by (auto simp add: l_coset_def m_assoc
                       subgroup.subset [THEN subsetD] subgroup.m_closed)
qed

lemma (in group) l_repr_independence:
  assumes y: "y \<in> x <# H" and x: "x \<in> carrier G" and sb: "subgroup H G"
  shows "x <# H = y <# H"
proof
  show "x <# H \<subseteq> y <# H"
    by (rule l_repr_imp_subset,
        (blast intro: l_coset_swap l_coset_carrier y x sb)+)
  show "y <# H \<subseteq> x <# H" by (rule l_repr_imp_subset [OF y x sb])
qed

lemma (in group) setmult_subset_G:
     "[| H \<subseteq> carrier G; K \<subseteq> carrier G |] ==> H <#> K \<subseteq> carrier G"
by (auto simp add: set_mult_eq subsetD)

lemma (in group) subgroup_mult_id: "subgroup H G ==> H <#> H = H"
apply (auto simp add: subgroup.m_closed set_mult_eq Sigma_def image_def)
apply (rule_tac x = x in bexI)
apply (rule bexI [of _ "\<one>"])
apply (auto simp add: subgroup.m_closed subgroup.one_closed
                      r_one subgroup.subset [THEN subsetD])
done


subsubsection {* Set of inverses of an @{text r_coset}. *}

lemma (in group) rcos_inv:
  assumes normalHG: "H <| G"
      and x:     "x \<in> carrier G"
  shows "set_inv G (H #> x) = H #> (inv x)"
proof -
  have H_subset: "H \<subseteq> carrier G"
    by (rule subgroup.subset [OF normal_imp_subgroup, OF normalHG])
  show ?thesis
  proof (auto simp add: r_coset_eq image_def set_inv_def)
    fix h
    assume "h \<in> H"
      hence "((inv x) \<otimes> (inv h) \<otimes> x) \<otimes> inv x = inv (h \<otimes> x)"
        by (simp add: x m_assoc inv_mult_group H_subset [THEN subsetD])
      thus "\<exists>j\<in>H. j \<otimes> inv x = inv (h \<otimes> x)"
       using prems
        by (blast intro: normal_inv_op_closed1 normal_imp_subgroup
                         subgroup.m_inv_closed)
  next
    fix h
    assume "h \<in> H"
      hence eq: "(x \<otimes> (inv h) \<otimes> (inv x)) \<otimes> x = x \<otimes> inv h"
        by (simp add: x m_assoc H_subset [THEN subsetD])
      hence "(\<exists>j\<in>H. j \<otimes> x = inv  (h \<otimes> (inv x))) \<and> h \<otimes> inv x = inv (inv (h \<otimes> (inv x)))"
       using prems
        by (simp add: m_assoc inv_mult_group H_subset [THEN subsetD],
            blast intro: eq normal_inv_op_closed2 normal_imp_subgroup
                         subgroup.m_inv_closed)
      thus "\<exists>y. (\<exists>h\<in>H. h \<otimes> x = y) \<and> h \<otimes> inv x = inv y" ..
  qed
qed

lemma (in group) rcos_inv2:
     "[| H <| G; K \<in> rcosets G H; x \<in> K |] ==> set_inv G K = H #> (inv x)"
apply (simp add: setrcos_eq, clarify)
apply (subgoal_tac "x : carrier G")
 prefer 2
 apply (blast dest: r_coset_subset_G subgroup.subset normal_imp_subgroup)
apply (drule repr_independence)
  apply assumption
 apply (erule normal_imp_subgroup)
apply (simp add: rcos_inv)
done


subsubsection {*Theorems for @{text "<#>"} with @{text "#>"} or @{text "<#"}.*}

lemma (in group) setmult_rcos_assoc:
     "[| H \<subseteq> carrier G; K \<subseteq> carrier G; x \<in> carrier G |]
      ==> H <#> (K #> x) = (H <#> K) #> x"
apply (auto simp add: r_coset_def set_mult_def)
apply (force simp add: m_assoc)+
done

lemma (in group) rcos_assoc_lcos:
     "[| H \<subseteq> carrier G; K \<subseteq> carrier G; x \<in> carrier G |]
      ==> (H #> x) <#> K = H <#> (x <# K)"
apply (auto simp add: r_coset_def l_coset_def set_mult_def Sigma_def image_def)
apply (force intro!: exI bexI simp add: m_assoc)+
done

lemma (in group) rcos_mult_step1:
     "[| H <| G; x \<in> carrier G; y \<in> carrier G |]
      ==> (H #> x) <#> (H #> y) = (H <#> (x <# H)) #> y"
by (simp add: setmult_rcos_assoc normal_imp_subgroup [THEN subgroup.subset]
              r_coset_subset_G l_coset_subset_G rcos_assoc_lcos)

lemma (in group) rcos_mult_step2:
     "[| H <| G; x \<in> carrier G; y \<in> carrier G |]
      ==> (H <#> (x <# H)) #> y = (H <#> (H #> x)) #> y"
by (simp add: normal_def)

lemma (in group) rcos_mult_step3:
     "[| H <| G; x \<in> carrier G; y \<in> carrier G |]
      ==> (H <#> (H #> x)) #> y = H #> (x \<otimes> y)"
by (simp add: setmult_rcos_assoc r_coset_subset_G coset_mult_assoc
              setmult_subset_G  subgroup_mult_id
              subgroup.subset normal_imp_subgroup)

lemma (in group) rcos_sum:
     "[| H <| G; x \<in> carrier G; y \<in> carrier G |]
      ==> (H #> x) <#> (H #> y) = H #> (x \<otimes> y)"
by (simp add: rcos_mult_step1 rcos_mult_step2 rcos_mult_step3)

lemma (in group) setrcos_mult_eq: "[|H <| G; M \<in> rcosets G H|] ==> H <#> M = M"
  -- {* generalizes @{text subgroup_mult_id} *}
  by (auto simp add: setrcos_eq normal_imp_subgroup subgroup.subset
    setmult_rcos_assoc subgroup_mult_id)


subsubsection{*Two distinct right cosets are disjoint*}

lemma (in group) rcos_equation:
     "[|subgroup H G;  a \<in> carrier G;  b \<in> carrier G;  ha \<otimes> a = h \<otimes> b;
        h \<in> H;  ha \<in> H;  hb \<in> H|]
      ==> \<exists>h\<in>H. h \<otimes> b = hb \<otimes> a"
apply (rule bexI [of _"hb \<otimes> ((inv ha) \<otimes> h)"])
apply (simp  add: m_assoc transpose_inv subgroup.subset [THEN subsetD])
apply (simp add: subgroup.m_closed subgroup.m_inv_closed)
done

lemma (in group) rcos_disjoint:
     "[|subgroup H G; a \<in> rcosets G H; b \<in> rcosets G H; a\<noteq>b|] ==> a \<inter> b = {}"
apply (simp add: setrcos_eq r_coset_eq)
apply (blast intro: rcos_equation sym)
done


subsection {*Order of a Group and Lagrange's Theorem*}

constdefs
  order :: "('a, 'b) semigroup_scheme => nat"
  "order S == card (carrier S)"

lemma (in group) setrcos_part_G: "subgroup H G ==> \<Union>rcosets G H = carrier G"
apply (rule equalityI)
apply (force simp add: subgroup.subset [THEN subsetD]
                       setrcos_eq r_coset_def)
apply (auto simp add: setrcos_eq subgroup.subset rcos_self)
done

lemma (in group) cosets_finite:
     "[| c \<in> rcosets G H;  H \<subseteq> carrier G;  finite (carrier G) |] ==> finite c"
apply (auto simp add: setrcos_eq)
apply (simp (no_asm_simp) add: r_coset_subset_G [THEN finite_subset])
done

text{*The next two lemmas support the proof of @{text card_cosets_equal}.*}
lemma (in group) inj_on_f:
    "[|H \<subseteq> carrier G;  a \<in> carrier G|] ==> inj_on (\<lambda>y. y \<otimes> inv a) (H #> a)"
apply (rule inj_onI)
apply (subgoal_tac "x \<in> carrier G & y \<in> carrier G")
 prefer 2 apply (blast intro: r_coset_subset_G [THEN subsetD])
apply (simp add: subsetD)
done

lemma (in group) inj_on_g:
    "[|H \<subseteq> carrier G;  a \<in> carrier G|] ==> inj_on (\<lambda>y. y \<otimes> a) H"
by (force simp add: inj_on_def subsetD)

lemma (in group) card_cosets_equal:
     "[| c \<in> rcosets G H;  H \<subseteq> carrier G; finite(carrier G) |]
      ==> card c = card H"
apply (auto simp add: setrcos_eq)
apply (rule card_bij_eq)
     apply (rule inj_on_f, assumption+)
    apply (force simp add: m_assoc subsetD r_coset_def)
   apply (rule inj_on_g, assumption+)
  apply (force simp add: m_assoc subsetD r_coset_def)
 txt{*The sets @{term "H #> a"} and @{term "H"} are finite.*}
 apply (simp add: r_coset_subset_G [THEN finite_subset])
apply (blast intro: finite_subset)
done

lemma (in group) setrcos_subset_PowG:
     "subgroup H G  ==> rcosets G H \<subseteq> Pow(carrier G)"
apply (simp add: setrcos_eq)
apply (blast dest: r_coset_subset_G subgroup.subset)
done


theorem (in group) lagrange:
     "[| finite(carrier G); subgroup H G |]
      ==> card(rcosets G H) * card(H) = order(G)"
apply (simp (no_asm_simp) add: order_def setrcos_part_G [symmetric])
apply (subst mult_commute)
apply (rule card_partition)
   apply (simp add: setrcos_subset_PowG [THEN finite_subset])
  apply (simp add: setrcos_part_G)
 apply (simp add: card_cosets_equal subgroup.subset)
apply (simp add: rcos_disjoint)
done


subsection {*Quotient Groups: Factorization of a Group*}

constdefs
  FactGroup :: "[('a,'b) monoid_scheme, 'a set] => ('a set) monoid"
     (infixl "Mod" 65)
    --{*Actually defined for groups rather than monoids*}
  "FactGroup G H ==
    (| carrier = rcosets G H, mult = set_mult G, one = H |)"

lemma (in group) setmult_closed:
     "[| H <| G; K1 \<in> rcosets G H; K2 \<in> rcosets G H |]
      ==> K1 <#> K2 \<in> rcosets G H"
by (auto simp add: normal_imp_subgroup [THEN subgroup.subset]
                   rcos_sum setrcos_eq)

lemma (in group) setinv_closed:
     "[| H <| G; K \<in> rcosets G H |] ==> set_inv G K \<in> rcosets G H"
by (auto simp add: normal_imp_subgroup
                   subgroup.subset rcos_inv
                   setrcos_eq)

lemma (in group) setrcos_assoc:
     "[|H <| G; M1 \<in> rcosets G H; M2 \<in> rcosets G H; M3 \<in> rcosets G H|]
      ==> M1 <#> M2 <#> M3 = M1 <#> (M2 <#> M3)"
by (auto simp add: setrcos_eq rcos_sum normal_imp_subgroup
                   subgroup.subset m_assoc)

lemma (in group) subgroup_in_rcosets:
  "subgroup H G ==> H \<in> rcosets G H"
proof -
  assume sub: "subgroup H G"
  have "r_coset G H \<one> = H"
    by (rule coset_join2)
       (auto intro: sub subgroup.one_closed)
  then show ?thesis
    by (auto simp add: setrcos_eq)
qed

lemma (in group) setrcos_inv_mult_group_eq:
     "[|H <| G; M \<in> rcosets G H|] ==> set_inv G M <#> M = H"
by (auto simp add: setrcos_eq rcos_inv rcos_sum normal_imp_subgroup
                   subgroup.subset)
(*
lemma (in group) factorgroup_is_magma:
  "H <| G ==> magma (G Mod H)"
  by rule (simp add: FactGroup_def coset.setmult_closed [OF is_coset])

lemma (in group) factorgroup_semigroup_axioms:
  "H <| G ==> semigroup_axioms (G Mod H)"
  by rule (simp add: FactGroup_def coset.setrcos_assoc [OF is_coset]
    coset.setmult_closed [OF is_coset])
*)
theorem (in group) factorgroup_is_group:
  "H <| G ==> group (G Mod H)"
apply (simp add: FactGroup_def)
apply (rule groupI)
    apply (simp add: setmult_closed)
   apply (simp add: normal_imp_subgroup subgroup_in_rcosets)
  apply (simp add: restrictI setmult_closed setrcos_assoc)
 apply (simp add: normal_imp_subgroup
                  subgroup_in_rcosets setrcos_mult_eq)
apply (auto dest: setrcos_inv_mult_group_eq simp add: setinv_closed)
done

lemma mult_FactGroup [simp]: "X \<otimes>\<^bsub>(G Mod H)\<^esub> X' = X <#>\<^bsub>G\<^esub> X'"
  by (simp add: FactGroup_def) 

lemma (in group) inv_FactGroup:
     "N <| G ==> X \<in> carrier (G Mod N) ==> inv\<^bsub>G Mod N\<^esub> X = set_inv G X"
apply (rule group.inv_equality [OF factorgroup_is_group]) 
apply (simp_all add: FactGroup_def setinv_closed setrcos_inv_mult_group_eq)
done

text{*The coset map is a homomorphism from @{term G} to the quotient group
  @{term "G Mod N"}*}
lemma (in group) r_coset_hom_Mod:
  assumes N: "N <| G"
  shows "(r_coset G N) \<in> hom G (G Mod N)"
by (simp add: FactGroup_def rcosets_def Pi_def hom_def rcos_sum N) 


subsection{*Quotienting by the Kernel of a Homomorphism*}

constdefs
  kernel :: "('a, 'm) monoid_scheme => ('b, 'n) monoid_scheme => 
             ('a => 'b) => 'a set" 
    --{*the kernel of a homomorphism*}
  "kernel G H h == {x. x \<in> carrier G & h x = \<one>\<^bsub>H\<^esub>}";

lemma (in group_hom) subgroup_kernel: "subgroup (kernel G H h) G"
apply (rule group.subgroupI) 
apply (auto simp add: kernel_def group.intro prems) 
done

text{*The kernel of a homomorphism is a normal subgroup*}
lemma (in group_hom) normal_kernel: "(kernel G H h) <| G"
apply (simp add: group.normal_inv_iff subgroup_kernel group.intro prems)
apply (simp add: kernel_def)  
done

lemma (in group_hom) FactGroup_nonempty:
  assumes X: "X \<in> carrier (G Mod kernel G H h)"
  shows "X \<noteq> {}"
proof -
  from X
  obtain g where "g \<in> carrier G" 
             and "X = kernel G H h #> g"
    by (auto simp add: FactGroup_def rcosets_def)
  thus ?thesis 
   by (force simp add: kernel_def r_coset_def image_def intro: hom_one)
qed


lemma (in group_hom) FactGroup_contents_mem:
  assumes X: "X \<in> carrier (G Mod (kernel G H h))"
  shows "contents (h`X) \<in> carrier H"
proof -
  from X
  obtain g where g: "g \<in> carrier G" 
             and "X = kernel G H h #> g"
    by (auto simp add: FactGroup_def rcosets_def)
  hence "h ` X = {h g}" by (force simp add: kernel_def r_coset_def image_def g)
  thus ?thesis by (auto simp add: g)
qed

lemma (in group_hom) FactGroup_hom:
     "(%X. contents (h`X)) \<in> hom (G Mod (kernel G H h)) H"
proof (simp add: hom_def funcsetI FactGroup_contents_mem, intro ballI) 
  fix X and X'
  assume X:  "X  \<in> carrier (G Mod kernel G H h)"
     and X': "X' \<in> carrier (G Mod kernel G H h)"
  then
  obtain g and g'
           where "g \<in> carrier G" and "g' \<in> carrier G" 
             and "X = kernel G H h #> g" and "X' = kernel G H h #> g'"
    by (auto simp add: FactGroup_def rcosets_def)
  hence all: "\<forall>x\<in>X. h x = h g" "\<forall>x\<in>X'. h x = h g'" 
    and Xsub: "X \<subseteq> carrier G" and X'sub: "X' \<subseteq> carrier G"
    by (force simp add: kernel_def r_coset_def image_def)+
  hence "h ` (X <#> X') = {h g \<otimes>\<^bsub>H\<^esub> h g'}" using X X'
    by (auto dest!: FactGroup_nonempty
             simp add: set_mult_def image_eq_UN 
                       subsetD [OF Xsub] subsetD [OF X'sub]) 
  thus "contents (h ` (X <#> X')) = contents (h ` X) \<otimes>\<^bsub>H\<^esub> contents (h ` X')"
    by (simp add: all image_eq_UN FactGroup_nonempty X X')  
qed

text{*Lemma for the following injectivity result*}
lemma (in group_hom) FactGroup_subset:
     "[|g \<in> carrier G; g' \<in> carrier G; h g = h g'|]
      ==>  kernel G H h #> g \<subseteq> kernel G H h #> g'"
apply (clarsimp simp add: kernel_def r_coset_def image_def);
apply (rename_tac y)  
apply (rule_tac x="y \<otimes> g \<otimes> inv g'" in exI) 
apply (simp add: G.m_assoc); 
done

lemma (in group_hom) FactGroup_inj_on:
     "inj_on (\<lambda>X. contents (h ` X)) (carrier (G Mod kernel G H h))"
proof (simp add: inj_on_def, clarify) 
  fix X and X'
  assume X:  "X  \<in> carrier (G Mod kernel G H h)"
     and X': "X' \<in> carrier (G Mod kernel G H h)"
  then
  obtain g and g'
           where gX: "g \<in> carrier G"  "g' \<in> carrier G" 
              "X = kernel G H h #> g" "X' = kernel G H h #> g'"
    by (auto simp add: FactGroup_def rcosets_def)
  hence all: "\<forall>x\<in>X. h x = h g" "\<forall>x\<in>X'. h x = h g'" 
    by (force simp add: kernel_def r_coset_def image_def)+
  assume "contents (h ` X) = contents (h ` X')"
  hence h: "h g = h g'"
    by (simp add: image_eq_UN all FactGroup_nonempty X X') 
  show "X=X'" by (rule equalityI) (simp_all add: FactGroup_subset h gX) 
qed

text{*If the homomorphism @{term h} is onto @{term H}, then so is the
homomorphism from the quotient group*}
lemma (in group_hom) FactGroup_onto:
  assumes h: "h ` carrier G = carrier H"
  shows "(\<lambda>X. contents (h ` X)) ` carrier (G Mod kernel G H h) = carrier H"
proof
  show "(\<lambda>X. contents (h ` X)) ` carrier (G Mod kernel G H h) \<subseteq> carrier H"
    by (auto simp add: FactGroup_contents_mem)
  show "carrier H \<subseteq> (\<lambda>X. contents (h ` X)) ` carrier (G Mod kernel G H h)"
  proof
    fix y
    assume y: "y \<in> carrier H"
    with h obtain g where g: "g \<in> carrier G" "h g = y"
      by (blast elim: equalityE); 
    hence "(\<Union>\<^bsub>x\<in>kernel G H h #> g\<^esub> {h x}) = {y}" 
      by (auto simp add: y kernel_def r_coset_def) 
    with g show "y \<in> (\<lambda>X. contents (h ` X)) ` carrier (G Mod kernel G H h)" 
      by (auto intro!: bexI simp add: FactGroup_def rcosets_def image_eq_UN)
  qed
qed


text{*If @{term h} is a homomorphism from @{term G} onto @{term H}, then the
 quotient group @{term "G Mod (kernel G H h)"} is isomorphic to @{term H}.*}
theorem (in group_hom) FactGroup_iso:
  "h ` carrier G = carrier H
   \<Longrightarrow> (%X. contents (h`X)) \<in> (G Mod (kernel G H h)) \<cong> H"
by (simp add: iso_def FactGroup_hom FactGroup_inj_on bij_betw_def 
              FactGroup_onto) 

end
