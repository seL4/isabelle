(*  Title:      HOL/GroupTheory/Coset
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
*)

header{*Theory of Cosets*}

theory Coset = Group + Exponent:

declare (in group) l_inv [simp]  r_inv [simp] 

constdefs
  r_coset    :: "[('a,'b) monoid_scheme,'a set, 'a] => 'a set"    
   "r_coset G H a == (% x. (mult G) x a) ` H"

  l_coset    :: "[('a,'b) monoid_scheme, 'a, 'a set] => 'a set"
   "l_coset G a H == (% x. (mult G) a x) ` H"

  rcosets  :: "[('a,'b) monoid_scheme,'a set] => ('a set)set"
   "rcosets G H == r_coset G H ` (carrier G)"

  set_mult  :: "[('a,'b) monoid_scheme,'a set,'a set] => 'a set"
   "set_mult G H K == (%(x,y). (mult G) x y) ` (H \<times> K)"

  set_inv   :: "[('a,'b) monoid_scheme,'a set] => 'a set"
   "set_inv G H == (m_inv G) ` H"

  normal     :: "['a set, ('a,'b) monoid_scheme] => bool"       (infixl "<|" 60)
   "normal H G == subgroup H G & 
                  (\<forall>x \<in> carrier G. r_coset G H x = l_coset G x H)"

syntax (xsymbols)
  normal  :: "['a set, ('a,'b) monoid_scheme] => bool" (infixl "\<lhd>" 60)

locale coset = group G +
  fixes rcos      :: "['a set, 'a] => 'a set"     (infixl "#>" 60)
    and lcos      :: "['a, 'a set] => 'a set"     (infixl "<#" 60)
    and setmult   :: "['a set, 'a set] => 'a set" (infixl "<#>" 60)
  defines rcos_def: "H #> x == r_coset G H x"
      and lcos_def: "x <# H == l_coset G x H"
      and setmult_def: "H <#> K == set_mult G H K"

text {*
  Locale @{term coset} provides only syntax.
  Logically, groups are cosets.
*}
lemma (in group) is_coset:
  "coset G"
  ..

text{*Lemmas useful for Sylow's Theorem*}

lemma card_inj:
     "[|f \<in> A\<rightarrow>B; inj_on f A; finite A; finite B|] ==> card(A) <= card(B)"
apply (rule card_inj_on_le)
apply (auto simp add: Pi_def)
done

lemma card_bij: 
     "[|f \<in> A\<rightarrow>B; inj_on f A; 
        g \<in> B\<rightarrow>A; inj_on g B; finite A; finite B|] ==> card(A) = card(B)"
by (blast intro: card_inj order_antisym) 


subsection{*Lemmas Using Locale Constants*}

lemma (in coset) r_coset_eq: "H #> a = {b . \<exists>h\<in>H. h \<otimes> a = b}"
by (auto simp add: rcos_def r_coset_def)

lemma (in coset) l_coset_eq: "a <# H = {b . \<exists>h\<in>H. a \<otimes> h = b}"
by (auto simp add: lcos_def l_coset_def)

lemma (in coset) setrcos_eq: "rcosets G H = {C . \<exists>a\<in>carrier G. C = H #> a}"
by (auto simp add: rcosets_def rcos_def)

lemma (in coset) set_mult_eq: "H <#> K = {c . \<exists>h\<in>H. \<exists>k\<in>K. c = h \<otimes> k}"
by (simp add: setmult_def set_mult_def image_def)

lemma (in coset) coset_mult_assoc:
     "[| M <= carrier G; g \<in> carrier G; h \<in> carrier G |]  
      ==> (M #> g) #> h = M #> (g \<otimes> h)"
by (force simp add: r_coset_eq m_assoc)

lemma (in coset) coset_mult_one [simp]: "M <= carrier G ==> M #> \<one> = M"
by (force simp add: r_coset_eq)

lemma (in coset) coset_mult_inv1:
     "[| M #> (x \<otimes> (inv y)) = M;  x \<in> carrier G ; y \<in> carrier G; 
         M <= carrier G |] ==> M #> x = M #> y"
apply (erule subst [of concl: "%z. M #> x = z #> y"])
apply (simp add: coset_mult_assoc m_assoc)
done

lemma (in coset) coset_mult_inv2:
     "[| M #> x = M #> y;  x \<in> carrier G;  y \<in> carrier G;  M <= carrier G |]  
      ==> M #> (x \<otimes> (inv y)) = M "
apply (simp add: coset_mult_assoc [symmetric])
apply (simp add: coset_mult_assoc)
done

lemma (in coset) coset_join1:
     "[| H #> x = H;  x \<in> carrier G;  subgroup H G |] ==> x\<in>H"
apply (erule subst)
apply (simp add: r_coset_eq)
apply (blast intro: l_one subgroup.one_closed)
done

text{*Locales don't currently work with @{text rule_tac}, so we
must prove this lemma separately.*}
lemma (in coset) solve_equation:
    "\<lbrakk>subgroup H G; x \<in> H; y \<in> H\<rbrakk> \<Longrightarrow> \<exists>h\<in>H. h \<otimes> x = y"
apply (rule bexI [of _ "y \<otimes> (inv x)"])
apply (auto simp add: subgroup.m_closed subgroup.m_inv_closed m_assoc 
                      subgroup.subset [THEN subsetD])
done

lemma (in coset) coset_join2:
     "[| x \<in> carrier G;  subgroup H G;  x\<in>H |] ==> H #> x = H"
by (force simp add: subgroup.m_closed r_coset_eq solve_equation)

lemma (in coset) r_coset_subset_G:
     "[| H <= carrier G; x \<in> carrier G |] ==> H #> x <= carrier G"
by (auto simp add: r_coset_eq)

lemma (in coset) rcosI:
     "[| h \<in> H; H <= carrier G; x \<in> carrier G|] ==> h \<otimes> x \<in> H #> x"
by (auto simp add: r_coset_eq)

lemma (in coset) setrcosI:
     "[| H <= carrier G; x \<in> carrier G |] ==> H #> x \<in> rcosets G H"
by (auto simp add: setrcos_eq)


text{*Really needed?*}
lemma (in coset) transpose_inv:
     "[| x \<otimes> y = z;  x \<in> carrier G;  y \<in> carrier G;  z \<in> carrier G |]  
      ==> (inv x) \<otimes> z = y"
by (force simp add: m_assoc [symmetric])

lemma (in coset) repr_independence:
     "[| y \<in> H #> x;  x \<in> carrier G; subgroup H G |] ==> H #> x = H #> y"
by (auto simp add: r_coset_eq m_assoc [symmetric] 
                   subgroup.subset [THEN subsetD]
                   subgroup.m_closed solve_equation)

lemma (in coset) rcos_self: "[| x \<in> carrier G; subgroup H G |] ==> x \<in> H #> x"
apply (simp add: r_coset_eq)
apply (blast intro: l_one subgroup.subset [THEN subsetD] 
                    subgroup.one_closed)
done


subsection{*normal subgroups*}

(*????????????????
text "Allows use of theorems proved in the locale coset"
lemma subgroup_imp_coset: "subgroup H G ==> coset G"
apply (drule subgroup_imp_group)
apply (simp add: group_def coset_def)  
done
*)

lemma normal_imp_subgroup: "H <| G ==> subgroup H G"
by (simp add: normal_def)


(*????????????????
lemmas normal_imp_group = normal_imp_subgroup [THEN subgroup_imp_group]
lemmas normal_imp_coset = normal_imp_subgroup [THEN subgroup_imp_coset]
*)

lemma (in coset) normal_iff:
     "(H <| G) = (subgroup H G & (\<forall>x \<in> carrier G. H #> x = x <# H))"
by (simp add: lcos_def rcos_def normal_def)

lemma (in coset) normal_imp_rcos_eq_lcos:
     "[| H <| G; x \<in> carrier G |] ==> H #> x = x <# H"
by (simp add: lcos_def rcos_def normal_def)

lemma (in coset) normal_inv_op_closed1:
     "\<lbrakk>H \<lhd> G; x \<in> carrier G; h \<in> H\<rbrakk> \<Longrightarrow> (inv x) \<otimes> h \<otimes> x \<in> H"
apply (auto simp add: l_coset_eq r_coset_eq normal_iff)
apply (drule bspec, assumption) 
apply (drule equalityD1 [THEN subsetD], blast, clarify)
apply (simp add: m_assoc subgroup.subset [THEN subsetD])
apply (erule subst)
apply (simp add: m_assoc [symmetric] subgroup.subset [THEN subsetD])
done

lemma (in coset) normal_inv_op_closed2:
     "\<lbrakk>H \<lhd> G; x \<in> carrier G; h \<in> H\<rbrakk> \<Longrightarrow> x \<otimes> h \<otimes> (inv x) \<in> H"
apply (drule normal_inv_op_closed1 [of H "(inv x)"]) 
apply auto
done

lemma (in coset) lcos_m_assoc:
     "[| M <= carrier G; g \<in> carrier G; h \<in> carrier G |]  
      ==> g <# (h <# M) = (g \<otimes> h) <# M"
by (force simp add: l_coset_eq m_assoc)

lemma (in coset) lcos_mult_one: "M <= carrier G ==> \<one> <# M = M"
by (force simp add: l_coset_eq)

lemma (in coset) l_coset_subset_G:
     "[| H <= carrier G; x \<in> carrier G |] ==> x <# H <= carrier G"
by (auto simp add: l_coset_eq subsetD)

lemma (in coset) l_repr_independence:
     "[| y \<in> x <# H;  x \<in> carrier G;  subgroup H G |] ==> x <# H = y <# H"
apply (auto simp add: l_coset_eq m_assoc 
                      subgroup.subset [THEN subsetD] subgroup.m_closed)
apply (rule_tac x = "mult G (m_inv G h) ha" in bexI)
  --{*FIXME: locales don't currently work with @{text rule_tac},
      want @{term "(inv h) \<otimes> ha"}*}
apply (auto simp add: m_assoc [symmetric] subgroup.subset [THEN subsetD] 
                      subgroup.m_inv_closed subgroup.m_closed)
done

lemma (in coset) setmult_subset_G:
     "[| H <= carrier G; K <= carrier G |] ==> H <#> K <= carrier G"
by (auto simp add: set_mult_eq subsetD)

lemma (in coset) subgroup_mult_id: "subgroup H G ==> H <#> H = H"
apply (auto simp add: subgroup.m_closed set_mult_eq Sigma_def image_def)
apply (rule_tac x = x in bexI)
apply (rule bexI [of _ "\<one>"])
apply (auto simp add: subgroup.m_closed subgroup.one_closed 
                      r_one subgroup.subset [THEN subsetD])
done


(* set of inverses of an r_coset *)
lemma (in coset) rcos_inv:
  assumes normalHG: "H <| G"
      and xinG:     "x \<in> carrier G"
  shows "set_inv G (H #> x) = H #> (inv x)"
proof -
  have H_subset: "H <= carrier G" 
    by (rule subgroup.subset [OF normal_imp_subgroup, OF normalHG])
  show ?thesis
  proof (auto simp add: r_coset_eq image_def set_inv_def)
    fix h
    assume "h \<in> H"
      hence "((inv x) \<otimes> (inv h) \<otimes> x) \<otimes> inv x = inv (h \<otimes> x)"
	by (simp add: xinG m_assoc inv_mult_group H_subset [THEN subsetD])
      thus "\<exists>j\<in>H. j \<otimes> inv x = inv (h \<otimes> x)" 
       using prems
	by (blast intro: normal_inv_op_closed1 normal_imp_subgroup 
			 subgroup.m_inv_closed)
  next
    fix h
    assume "h \<in> H"
      hence eq: "(x \<otimes> (inv h) \<otimes> (inv x)) \<otimes> x = x \<otimes> inv h"
        by (simp add: xinG m_assoc H_subset [THEN subsetD])
      hence "(\<exists>j\<in>H. j \<otimes> x = inv  (h \<otimes> (inv x))) \<and> h \<otimes> inv x = inv (inv (h \<otimes> (inv x)))"
       using prems
	by (simp add: m_assoc inv_mult_group H_subset [THEN subsetD],
            blast intro: eq normal_inv_op_closed2 normal_imp_subgroup 
			 subgroup.m_inv_closed)
      thus "\<exists>y. (\<exists>h\<in>H. h \<otimes> x = y) \<and> h \<otimes> inv x = inv y" ..
  qed
qed

(*The old proof is something like this, but the rule_tac calls make
illegal references to implicit structures.
lemma (in coset) rcos_inv:
     "[| H <| G; x \<in> carrier G |] ==> set_inv G (H #> x) = H #> (inv x)"
apply (frule normal_imp_subgroup)
apply (auto simp add: r_coset_eq image_def set_inv_def)
apply (rule_tac x = "(inv x) \<otimes> (inv h) \<otimes> x" in bexI)
apply (simp add: m_assoc inv_mult_group subgroup.subset [THEN subsetD])
apply (simp add: subgroup.m_inv_closed, assumption+)
apply (rule_tac x = "inv  (h \<otimes> (inv x)) " in exI)
apply (simp add: inv_mult_group subgroup.subset [THEN subsetD])
apply (rule_tac x = "x \<otimes> (inv h) \<otimes> (inv x)" in bexI)
apply (simp add: m_assoc subgroup.subset [THEN subsetD])
apply (simp add: normal_inv_op_closed2 subgroup.m_inv_closed)
done
*)

lemma (in coset) rcos_inv2:
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


(* some rules for <#> with #> or <# *)
lemma (in coset) setmult_rcos_assoc:
     "[| H <= carrier G; K <= carrier G; x \<in> carrier G |] 
      ==> H <#> (K #> x) = (H <#> K) #> x"
apply (auto simp add: rcos_def r_coset_def setmult_def set_mult_def)
apply (force simp add: m_assoc)+
done

lemma (in coset) rcos_assoc_lcos:
     "[| H <= carrier G; K <= carrier G; x \<in> carrier G |] 
      ==> (H #> x) <#> K = H <#> (x <# K)"
apply (auto simp add: rcos_def r_coset_def lcos_def l_coset_def 
                      setmult_def set_mult_def Sigma_def image_def)
apply (force intro!: exI bexI simp add: m_assoc)+
done

lemma (in coset) rcos_mult_step1:
     "[| H <| G; x \<in> carrier G; y \<in> carrier G |] 
      ==> (H #> x) <#> (H #> y) = (H <#> (x <# H)) #> y"
by (simp add: setmult_rcos_assoc normal_imp_subgroup [THEN subgroup.subset]
              r_coset_subset_G l_coset_subset_G rcos_assoc_lcos)

lemma (in coset) rcos_mult_step2:
     "[| H <| G; x \<in> carrier G; y \<in> carrier G |] 
      ==> (H <#> (x <# H)) #> y = (H <#> (H #> x)) #> y"
by (simp add: normal_imp_rcos_eq_lcos)

lemma (in coset) rcos_mult_step3:
     "[| H <| G; x \<in> carrier G; y \<in> carrier G |] 
      ==> (H <#> (H #> x)) #> y = H #> (x \<otimes> y)"
by (simp add: setmult_rcos_assoc r_coset_subset_G coset_mult_assoc
              setmult_subset_G  subgroup_mult_id
              subgroup.subset normal_imp_subgroup)

lemma (in coset) rcos_sum:
     "[| H <| G; x \<in> carrier G; y \<in> carrier G |] 
      ==> (H #> x) <#> (H #> y) = H #> (x \<otimes> y)"
by (simp add: rcos_mult_step1 rcos_mult_step2 rcos_mult_step3)

(*generalizes subgroup_mult_id*)
lemma (in coset) setrcos_mult_eq: "[|H <| G; M \<in> rcosets G H|] ==> H <#> M = M"
by (auto simp add: setrcos_eq normal_imp_subgroup subgroup.subset
                   setmult_rcos_assoc subgroup_mult_id)


subsection{*Lemmas Leading to Lagrange's Theorem*}

lemma (in coset) setrcos_part_G: "subgroup H G ==> \<Union> rcosets G H = carrier G"
apply (rule equalityI)
apply (force simp add: subgroup.subset [THEN subsetD] 
                       setrcos_eq r_coset_eq)
apply (auto simp add: setrcos_eq subgroup.subset rcos_self)
done

lemma (in coset) cosets_finite:
     "[| c \<in> rcosets G H;  H <= carrier G;  finite (carrier G) |] ==> finite c"
apply (auto simp add: setrcos_eq)
apply (simp (no_asm_simp) add: r_coset_subset_G [THEN finite_subset])
done

text{*The next two lemmas support the proof of @{text card_cosets_equal},
since we can't use @{text rule_tac} with explicit terms for @{term f} and
@{term g}.*}
lemma (in coset) inj_on_f:
    "[|H \<subseteq> carrier G;  a \<in> carrier G|] ==> inj_on (\<lambda>y. y \<otimes> inv a) (H #> a)"
apply (rule inj_onI)
apply (subgoal_tac "x \<in> carrier G & y \<in> carrier G")
 prefer 2 apply (blast intro: r_coset_subset_G [THEN subsetD])
apply (simp add: subsetD)
done

lemma (in coset) inj_on_g:
    "[|H \<subseteq> carrier G;  a \<in> carrier G|] ==> inj_on (\<lambda>y. y \<otimes> a) H"
by (force simp add: inj_on_def subsetD)

lemma (in coset) card_cosets_equal:
     "[| c \<in> rcosets G H;  H <= carrier G; finite(carrier G) |] 
      ==> card c = card H"
apply (auto simp add: setrcos_eq)
apply (rule card_bij_eq)
     apply (rule inj_on_f, assumption+) 
    apply (force simp add: m_assoc subsetD r_coset_eq)
   apply (rule inj_on_g, assumption+) 
  apply (force simp add: m_assoc subsetD r_coset_eq)
 txt{*The sets @{term "H #> a"} and @{term "H"} are finite.*}
 apply (simp add: r_coset_subset_G [THEN finite_subset])
apply (blast intro: finite_subset)
done

subsection{*Two distinct right cosets are disjoint*}

lemma (in coset) rcos_equation:
     "[|subgroup H G;  a \<in> carrier G;  b \<in> carrier G;  ha \<otimes> a = h \<otimes> b;   
        h \<in> H;  ha \<in> H;  hb \<in> H|]  
      ==> \<exists>h\<in>H. h \<otimes> b = hb \<otimes> a"
apply (rule bexI [of _"hb \<otimes> ((inv ha) \<otimes> h)"])
apply (simp  add: m_assoc transpose_inv subgroup.subset [THEN subsetD])
apply (simp add: subgroup.m_closed subgroup.m_inv_closed)
done

lemma (in coset) rcos_disjoint:
     "[|subgroup H G; a \<in> rcosets G H; b \<in> rcosets G H; a\<noteq>b|] ==> a \<inter> b = {}"
apply (simp add: setrcos_eq r_coset_eq)
apply (blast intro: rcos_equation sym)
done

lemma (in coset) setrcos_subset_PowG:
     "subgroup H G  ==> rcosets G H <= Pow(carrier G)"
apply (simp add: setrcos_eq)
apply (blast dest: r_coset_subset_G subgroup.subset)
done

subsection {*Factorization of a Group*}

constdefs
  FactGroup :: "[('a,'b) monoid_scheme, 'a set] => ('a set) monoid"
     (infixl "Mod" 60)
   "FactGroup G H ==
      (| carrier = rcosets G H,
	 mult = (%X: rcosets G H. %Y: rcosets G H. set_mult G X Y),
	 one = H (*,
	 m_inv = (%X: rcosets G H. set_inv G X) *) |)"

lemma (in coset) setmult_closed:
     "[| H <| G; K1 \<in> rcosets G H; K2 \<in> rcosets G H |] 
      ==> K1 <#> K2 \<in> rcosets G H"
by (auto simp add: normal_imp_subgroup [THEN subgroup.subset] 
                   rcos_sum setrcos_eq)

lemma (in group) setinv_closed:
     "[| H <| G; K \<in> rcosets G H |] ==> set_inv G K \<in> rcosets G H"
by (auto simp add:  normal_imp_subgroup
                 subgroup.subset coset.rcos_inv [OF is_coset]
                 coset.setrcos_eq [OF is_coset])

(*
The old version is no longer valid: "group G" has to be an explicit premise.

lemma setinv_closed:
     "[| H <| G; K \<in> rcosets G H |] ==> set_inv G K \<in> rcosets G H"
by (auto simp add:  normal_imp_subgroup
                   subgroup.subset coset.rcos_inv coset.setrcos_eq)
*)

lemma (in coset) setrcos_assoc:
     "[|H <| G; M1 \<in> rcosets G H; M2 \<in> rcosets G H; M3 \<in> rcosets G H|]   
      ==> M1 <#> M2 <#> M3 = M1 <#> (M2 <#> M3)"
by (auto simp add: setrcos_eq rcos_sum normal_imp_subgroup 
                   subgroup.subset m_assoc)

lemma (in group) subgroup_in_rcosets:
  "subgroup H G ==> H \<in> rcosets G H"
proof -
  assume sub: "subgroup H G"
  have "r_coset G H \<one> = H"
    by (rule coset.coset_join2)
      (auto intro: sub subgroup.one_closed is_coset)
  then show ?thesis
    by (auto simp add: coset.setrcos_eq [OF is_coset])
qed

(*
lemma subgroup_in_rcosets:
  "subgroup H G ==> H \<in> rcosets G H"
apply (frule subgroup_imp_coset) 
apply (frule subgroup_imp_group) 
apply (simp add: coset.setrcos_eq)
apply (blast del: equalityI 
             intro!: group.subgroup.one_closed group.one_closed
                     coset.coset_join2 [symmetric])
done
*)

lemma (in coset) setrcos_inv_mult_group_eq:
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
apply (insert is_coset) 
apply (simp add: FactGroup_def) 
apply (rule groupI)
    apply (simp add: coset.setmult_closed)
   apply (simp add: normal_imp_subgroup subgroup_in_rcosets)
  apply (simp add: restrictI coset.setmult_closed coset.setrcos_assoc)
 apply (simp add: normal_imp_subgroup
   subgroup_in_rcosets coset.setrcos_mult_eq)
apply (auto dest: coset.setrcos_inv_mult_group_eq simp add: setinv_closed)
done

end
