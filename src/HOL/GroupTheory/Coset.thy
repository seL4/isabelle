(*  Title:      HOL/GroupTheory/Coset
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
*)

header{*Theory of Cosets*}

theory Coset = Group + Exponent:

constdefs
  r_coset    :: "[('a,'b) group_scheme,'a set, 'a] => 'a set"    
   "r_coset G H a == (% x. (sum G) x a) ` H"

  l_coset    :: "[('a,'b) group_scheme, 'a, 'a set] => 'a set"
   "l_coset G a H == (% x. (sum G) a x) ` H"

  rcosets  :: "[('a,'b) group_scheme,'a set] => ('a set)set"
   "rcosets G H == r_coset G H ` (carrier G)"

  set_sum  :: "[('a,'b) group_scheme,'a set,'a set] => 'a set"
   "set_sum G H K == (%(x,y). (sum G) x y) ` (H \<times> K)"

  set_minus   :: "[('a,'b) group_scheme,'a set] => 'a set"
   "set_minus G H == (gminus G) ` H"

  normal     :: "['a set, ('a,'b) group_scheme] => bool"       (infixl "<|" 60) 
   "normal H G == subgroup H G & 
                  (\<forall>x \<in> carrier G. r_coset G H x = l_coset G x H)"

syntax (xsymbols)
  normal  :: "['a set, ('a,'b) group_scheme] => bool" (infixl "\<lhd>" 60)

locale coset = group G +
  fixes rcos      :: "['a set, 'a] => 'a set"     (infixl "#>" 60)
    and lcos      :: "['a, 'a set] => 'a set"     (infixl "<#" 60)
    and setsum   :: "['a set, 'a set] => 'a set" (infixl "<#>" 60)
  defines rcos_def: "H #> x == r_coset G H x"
      and lcos_def: "x <# H == l_coset G x H"
      and setsum_def: "H <#> K == set_sum G H K"


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

lemma (in coset) r_coset_eq: "H #> a = {b . \<exists>h\<in>H. h \<oplus> a = b}"
by (auto simp add: rcos_def r_coset_def sum_def)

lemma (in coset) l_coset_eq: "a <# H = {b . \<exists>h\<in>H. a \<oplus> h = b}"
by (auto simp add: lcos_def l_coset_def sum_def)

lemma (in coset) setrcos_eq: "rcosets G H = {C . \<exists>a\<in>carrier G. C = H #> a}"
by (auto simp add: rcosets_def rcos_def sum_def)

lemma (in coset) set_sum_eq: "H <#> K = {c . \<exists>h\<in>H. \<exists>k\<in>K. c = h \<oplus> k}"
by (simp add: setsum_def set_sum_def sum_def image_def)

lemma (in coset) coset_sum_assoc:
     "[| M <= carrier G; g \<in> carrier G; h \<in> carrier G |]  
      ==> (M #> g) #> h = M #> (g \<oplus> h)"
by (force simp add: r_coset_eq sum_assoc)

lemma (in coset) coset_sum_zero [simp]: "M <= carrier G ==> M #> \<zero> = M"
by (force simp add: r_coset_eq)

lemma (in coset) coset_sum_minus1:
     "[| M #> (x \<oplus> (\<ominus>y)) = M;  x \<in> carrier G ; y \<in> carrier G; 
         M <= carrier G |] ==> M #> x = M #> y"
apply (erule subst [of concl: "%z. M #> x = z #> y"])
apply (simp add: coset_sum_assoc sum_assoc)
done

lemma (in coset) coset_sum_minus2:
     "[| M #> x = M #> y;  x \<in> carrier G;  y \<in> carrier G;  M <= carrier G |]  
      ==> M #> (x \<oplus> (\<ominus>y)) = M "
apply (simp add: coset_sum_assoc [symmetric])
apply (simp add: coset_sum_assoc)
done

lemma (in coset) coset_join1:
     "[| H #> x = H;  x \<in> carrier G;  subgroup H G |] ==> x\<in>H"
apply (erule subst)
apply (simp add: r_coset_eq)
apply (blast intro: left_zero subgroup_zero_closed)
done

text{*Locales don't currently work with @{text rule_tac}, so we
must prove this lemma separately.*}
lemma (in coset) solve_equation:
    "\<lbrakk>subgroup H G; x \<in> H; y \<in> H\<rbrakk> \<Longrightarrow> \<exists>h\<in>H. h \<oplus> x = y"
apply (rule bexI [of _ "y \<oplus> (\<ominus>x)"])
apply (auto simp add: subgroup_sum_closed subgroup_minus_closed sum_assoc 
                      subgroup_imp_subset [THEN subsetD])
done

lemma (in coset) coset_join2:
     "[| x \<in> carrier G;  subgroup H G;  x\<in>H |] ==> H #> x = H"
by (force simp add: subgroup_sum_closed r_coset_eq solve_equation)

lemma (in coset) r_coset_subset_G:
     "[| H <= carrier G; x \<in> carrier G |] ==> H #> x <= carrier G"
by (auto simp add: r_coset_eq)

lemma (in coset) rcosI:
     "[| h \<in> H; H <= carrier G; x \<in> carrier G|] ==> h \<oplus> x \<in> H #> x"
by (auto simp add: r_coset_eq)

lemma (in coset) setrcosI:
     "[| H <= carrier G; x \<in> carrier G |] ==> H #> x \<in> rcosets G H"
by (auto simp add: setrcos_eq)


text{*Really needed?*}
lemma (in coset) transpose_minus:
     "[| x \<oplus> y = z;  x \<in> carrier G;  y \<in> carrier G;  z \<in> carrier G |]  
      ==> (\<ominus>x) \<oplus> z = y"
by (force simp add: sum_assoc [symmetric])

lemma (in coset) repr_independence:
     "[| y \<in> H #> x;  x \<in> carrier G; subgroup H G |] ==> H #> x = H #> y"
by (auto simp add: r_coset_eq sum_assoc [symmetric] right_cancellation_iff
                   subgroup_imp_subset [THEN subsetD]
                   subgroup_sum_closed solve_equation)

lemma (in coset) rcos_self: "[| x \<in> carrier G; subgroup H G |] ==> x \<in> H #> x"
apply (simp add: r_coset_eq)
apply (blast intro: left_zero subgroup_imp_subset [THEN subsetD] 
                    subgroup_zero_closed)
done


subsection{*normal subgroups*}

text{*Allows use of theorems proved in the locale coset*}
lemma subgroup_imp_coset: "subgroup H G ==> coset G"
apply (drule subgroup_imp_group)
apply (simp add: group_def coset_def)  
done

lemma normal_imp_subgroup: "H <| G ==> subgroup H G"
by (simp add: normal_def)

lemmas normal_imp_group = normal_imp_subgroup [THEN subgroup_imp_group]
lemmas normal_imp_coset = normal_imp_subgroup [THEN subgroup_imp_coset]

lemma (in coset) normal_iff:
     "(H <| G) = (subgroup H G & (\<forall>x \<in> carrier G. H #> x = x <# H))"
by (simp add: lcos_def rcos_def normal_def)

lemma (in coset) normal_imp_rcos_eq_lcos:
     "[| H <| G; x \<in> carrier G |] ==> H #> x = x <# H"
by (simp add: lcos_def rcos_def normal_def)

lemma (in coset) normal_minus_op_closed1:
     "\<lbrakk>H \<lhd> G; x \<in> carrier G; h \<in> H\<rbrakk> \<Longrightarrow> (\<ominus>x) \<oplus> h \<oplus> x \<in> H"
apply (auto simp add: l_coset_eq r_coset_eq normal_iff)
apply (drule bspec, assumption) 
apply (drule equalityD1 [THEN subsetD], blast, clarify)
apply (simp add: sum_assoc subgroup_imp_subset [THEN subsetD])
apply (erule subst)
apply (simp add: sum_assoc [symmetric] subgroup_imp_subset [THEN subsetD])
done

lemma (in coset) normal_minus_op_closed2:
     "\<lbrakk>H \<lhd> G; x \<in> carrier G; h \<in> H\<rbrakk> \<Longrightarrow> x \<oplus> h \<oplus> (\<ominus>x) \<in> H"
apply (drule normal_minus_op_closed1 [of H "(\<ominus>x)"]) 
apply auto
done

lemma (in coset) lcos_sum_assoc:
     "[| M <= carrier G; g \<in> carrier G; h \<in> carrier G |]  
      ==> g <# (h <# M) = (g \<oplus> h) <# M"
by (force simp add: l_coset_eq sum_assoc)

lemma (in coset) lcos_sum_zero: "M <= carrier G ==> \<zero> <# M = M"
by (force simp add: l_coset_eq)

lemma (in coset) l_coset_subset_G:
     "[| H <= carrier G; x \<in> carrier G |] ==> x <# H <= carrier G"
by (auto simp add: l_coset_eq subsetD)

lemma (in coset) l_repr_independence:
     "[| y \<in> x <# H;  x \<in> carrier G;  subgroup H G |] ==> x <# H = y <# H"
apply (auto simp add: l_coset_eq sum_assoc 
                      subgroup_imp_subset [THEN subsetD] subgroup_sum_closed)
apply (rule_tac x = "sum G (gminus G h) ha" in bexI)
  --{*FIXME: locales don't currently work with @{text rule_tac},
      want @{term "(\<ominus>h) \<oplus> ha"}*}
apply (auto simp add: sum_assoc [symmetric] subgroup_imp_subset [THEN subsetD] 
                      subgroup_minus_closed subgroup_sum_closed)
done

lemma (in coset) setsum_subset_G:
     "[| H <= carrier G; K <= carrier G |] ==> H <#> K <= carrier G"
by (auto simp add: set_sum_eq subsetD)

lemma (in coset) subgroup_sum_id: "subgroup H G ==> H <#> H = H"
apply (auto simp add: subgroup_sum_closed set_sum_eq Sigma_def image_def)
apply (rule_tac x = x in bexI)
apply (rule bexI [of _ "\<zero>"])
apply (auto simp add: subgroup_sum_closed subgroup_zero_closed 
                      right_zero subgroup_imp_subset [THEN subsetD])
done


(* set of inverses of an r_coset *)
lemma (in coset) rcos_minus:
  assumes normalHG: "H <| G"
      and xinG:     "x \<in> carrier G"
  shows "set_minus G (H #> x) = H #> (\<ominus>x)"
proof -
  have H_subset: "H <= carrier G" 
    by (rule subgroup_imp_subset [OF normal_imp_subgroup, OF normalHG])
  show ?thesis
  proof (auto simp add: r_coset_eq image_def set_minus_def)
    fix h
    assume "h \<in> H"
      hence "((\<ominus>x) \<oplus> (\<ominus>h) \<oplus> x) \<oplus> \<ominus>x = \<ominus>(h \<oplus> x)"
	by (simp add: xinG sum_assoc minus_sum H_subset [THEN subsetD])
      thus "\<exists>j\<in>H. j \<oplus> \<ominus>x = \<ominus>(h \<oplus> x)" 
       using prems
	by (blast intro: normal_minus_op_closed1 normal_imp_subgroup 
			 subgroup_minus_closed)
  next
    fix h
    assume "h \<in> H"
      hence eq: "(x \<oplus> (\<ominus>h) \<oplus> (\<ominus>x)) \<oplus> x = x \<oplus> \<ominus>h"
        by (simp add: xinG sum_assoc H_subset [THEN subsetD])
      hence "(\<exists>j\<in>H. j \<oplus> x = \<ominus> (h \<oplus> (\<ominus>x))) \<and> h \<oplus> \<ominus>x = \<ominus>(\<ominus>(h \<oplus> (\<ominus>x)))"
       using prems
	by (simp add: sum_assoc minus_sum H_subset [THEN subsetD],
            blast intro: eq normal_minus_op_closed2 normal_imp_subgroup 
			 subgroup_minus_closed)
      thus "\<exists>y. (\<exists>h\<in>H. h \<oplus> x = y) \<and> h \<oplus> \<ominus>x = \<ominus>y" ..
  qed
qed

(*The old proof is something like this, but the rule_tac calls make
illegal references to implicit structures.
lemma (in coset) rcos_minus:
     "[| H <| G; x \<in> carrier G |] ==> set_minus G (H #> x) = H #> (\<ominus>x)"
apply (frule normal_imp_subgroup)
apply (auto simp add: r_coset_eq image_def set_minus_def)
apply (rule_tac x = "(\<ominus>x) \<oplus> (\<ominus>h) \<oplus> x" in bexI)
apply (simp add: sum_assoc minus_sum subgroup_imp_subset [THEN subsetD])
apply (simp add: subgroup_minus_closed, assumption+)
apply (rule_tac x = "\<ominus> (h \<oplus> (\<ominus>x)) " in exI)
apply (simp add: minus_sum subgroup_imp_subset [THEN subsetD])
apply (rule_tac x = "x \<oplus> (\<ominus>h) \<oplus> (\<ominus>x)" in bexI)
apply (simp add: sum_assoc subgroup_imp_subset [THEN subsetD])
apply (simp add: normal_minus_op_closed2 subgroup_minus_closed)
done
*)

lemma (in coset) rcos_minus2:
     "[| H <| G; K \<in> rcosets G H; x \<in> K |] ==> set_minus G K = H #> (\<ominus>x)"
apply (simp add: setrcos_eq, clarify)
apply (subgoal_tac "x : carrier G")
 prefer 2
 apply (blast dest: r_coset_subset_G subgroup_imp_subset normal_imp_subgroup) 
apply (drule repr_independence)
  apply assumption
 apply (erule normal_imp_subgroup)
apply (simp add: rcos_minus)
done


(* some rules for <#> with #> or <# *)
lemma (in coset) setsum_rcos_assoc:
     "[| H <= carrier G; K <= carrier G; x \<in> carrier G |] 
      ==> H <#> (K #> x) = (H <#> K) #> x"
apply (auto simp add: rcos_def r_coset_def setsum_def set_sum_def)
apply (force simp add: sum_assoc)+
done

lemma (in coset) rcos_assoc_lcos:
     "[| H <= carrier G; K <= carrier G; x \<in> carrier G |] 
      ==> (H #> x) <#> K = H <#> (x <# K)"
apply (auto simp add: rcos_def r_coset_def lcos_def l_coset_def 
                      setsum_def set_sum_def Sigma_def image_def)
apply (force intro!: exI bexI simp add: sum_assoc)+
done

lemma (in coset) rcos_sum_step1:
     "[| H <| G; x \<in> carrier G; y \<in> carrier G |] 
      ==> (H #> x) <#> (H #> y) = (H <#> (x <# H)) #> y"
by (simp add: setsum_rcos_assoc normal_imp_subgroup [THEN subgroup_imp_subset]
              r_coset_subset_G l_coset_subset_G rcos_assoc_lcos)

lemma (in coset) rcos_sum_step2:
     "[| H <| G; x \<in> carrier G; y \<in> carrier G |] 
      ==> (H <#> (x <# H)) #> y = (H <#> (H #> x)) #> y"
by (simp add: normal_imp_rcos_eq_lcos)

lemma (in coset) rcos_sum_step3:
     "[| H <| G; x \<in> carrier G; y \<in> carrier G |] 
      ==> (H <#> (H #> x)) #> y = H #> (x \<oplus> y)"
by (simp add: setsum_rcos_assoc r_coset_subset_G coset_sum_assoc
              setsum_subset_G  subgroup_sum_id
              subgroup_imp_subset normal_imp_subgroup)

lemma (in coset) rcos_sum:
     "[| H <| G; x \<in> carrier G; y \<in> carrier G |] 
      ==> (H #> x) <#> (H #> y) = H #> (x \<oplus> y)"
by (simp add: rcos_sum_step1 rcos_sum_step2 rcos_sum_step3)

(*generalizes subgroup_sum_id*)
lemma (in coset) setrcos_sum_eq: "[|H <| G; M \<in> rcosets G H|] ==> H <#> M = M"
by (auto simp add: setrcos_eq normal_imp_subgroup subgroup_imp_subset
                   setsum_rcos_assoc subgroup_sum_id)


subsection{*Lemmas Leading to Lagrange's Theorem*}

lemma (in coset) setrcos_part_G: "subgroup H G ==> \<Union> rcosets G H = carrier G"
apply (rule equalityI)
apply (force simp add: subgroup_imp_subset [THEN subsetD] 
                       setrcos_eq r_coset_eq)
apply (auto simp add: setrcos_eq subgroup_imp_subset rcos_self)
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
    "[|H \<subseteq> carrier G;  a \<in> carrier G|] ==> inj_on (\<lambda>y. y \<oplus> \<ominus>a) (H #> a)"
apply (rule inj_onI)
apply (subgoal_tac "x \<in> carrier G & y \<in> carrier G")
 prefer 2 apply (blast intro: r_coset_subset_G [THEN subsetD])
apply (rotate_tac -1)
apply (simp add: subsetD)
done

lemma (in coset) inj_on_g:
    "[|H \<subseteq> carrier G;  a \<in> carrier G|] ==> inj_on (\<lambda>y. y \<oplus> a) H"
by (force simp add: inj_on_def subsetD)

lemma (in coset) card_cosets_equal:
     "[| c \<in> rcosets G H;  H <= carrier G; finite(carrier G) |] 
      ==> card c = card H"
apply (auto simp add: setrcos_eq)
apply (rule card_bij_eq)
     apply (rule inj_on_f, assumption+) 
    apply (force simp add: sum_assoc subsetD r_coset_eq)
   apply (rule inj_on_g, assumption+) 
  apply (force simp add: sum_assoc subsetD r_coset_eq)
 txt{*The sets @{term "H #> a"} and @{term "H"} are finite.*}
 apply (simp add: r_coset_subset_G [THEN finite_subset])
apply (blast intro: finite_subset)
done

subsection{*Two distinct right cosets are disjoint*}

lemma (in coset) rcos_equation:
     "[|subgroup H G;  a \<in> carrier G;  b \<in> carrier G;  ha \<oplus> a = h \<oplus> b;   
        h \<in> H;  ha \<in> H;  hb \<in> H|]  
      ==> \<exists>h\<in>H. h \<oplus> b = hb \<oplus> a"
apply (rule bexI [of _"hb \<oplus> ((\<ominus>ha) \<oplus> h)"])
apply (simp  add: sum_assoc transpose_minus subgroup_imp_subset [THEN subsetD])
apply (simp add: subgroup_sum_closed subgroup_minus_closed)
done

lemma (in coset) rcos_disjoint:
     "[|subgroup H G; a \<in> rcosets G H; b \<in> rcosets G H; a\<noteq>b|] ==> a \<inter> b = {}"
apply (simp add: setrcos_eq r_coset_eq)
apply (blast intro: rcos_equation sym)
done

lemma (in coset) setrcos_subset_PowG:
     "subgroup H G  ==> rcosets G H <= Pow(carrier G)"
apply (simp add: setrcos_eq)
apply (blast dest: r_coset_subset_G subgroup_imp_subset)
done

theorem (in coset) lagrange:
     "[| finite(carrier G); subgroup H G |] 
      ==> card(rcosets G H) * card(H) = order(G)"
apply (simp (no_asm_simp) add: order_def setrcos_part_G [symmetric])
apply (subst mult_commute)
apply (rule card_partition)
   apply (simp add: setrcos_subset_PowG [THEN finite_subset])
  apply (simp add: setrcos_part_G)
 apply (simp add: card_cosets_equal subgroup_def)
apply (simp add: rcos_disjoint)
done


subsection {*Factorization of a Group*}

constdefs
  FactGroup :: "[('a,'b) group_scheme, 'a set] => ('a set) group"
     (infixl "Mod" 60)
   "FactGroup G H ==
      (| carrier = rcosets G H,
	 sum = (%X: rcosets G H. %Y: rcosets G H. set_sum G X Y),
	 gminus = (%X: rcosets G H. set_minus G X), 
	 zero = H |)"

lemma (in coset) setsum_closed:
     "[| H <| G; K1 \<in> rcosets G H; K2 \<in> rcosets G H |] 
      ==> K1 <#> K2 \<in> rcosets G H"
by (auto simp add: normal_imp_subgroup [THEN subgroup_imp_subset] 
                   rcos_sum setrcos_eq)

lemma setminus_closed:
     "[| H <| G; K \<in> rcosets G H |] ==> set_minus G K \<in> rcosets G H"
by (auto simp add: normal_imp_coset normal_imp_group normal_imp_subgroup
                   subgroup_imp_subset coset.rcos_minus coset.setrcos_eq)

lemma (in coset) setrcos_assoc:
     "[|H <| G; M1 \<in> rcosets G H; M2 \<in> rcosets G H; M3 \<in> rcosets G H|]   
      ==> M1 <#> M2 <#> M3 = M1 <#> (M2 <#> M3)"
by (auto simp add: setrcos_eq rcos_sum normal_imp_subgroup 
                   subgroup_imp_subset sum_assoc)

lemma subgroup_in_rcosets: "subgroup H G ==> H \<in> rcosets G H"
apply (frule subgroup_imp_coset) 
apply (frule subgroup_imp_group) 
apply (simp add: coset.setrcos_eq)
apply (blast del: equalityI 
             intro!: group.subgroup_zero_closed group.zero_closed
                     coset.coset_join2 [symmetric])
done

lemma (in coset) setrcos_minus_sum_eq:
     "[|H <| G; M \<in> rcosets G H|] ==> set_minus G M <#> M = H"
by (auto simp add: setrcos_eq rcos_minus rcos_sum normal_imp_subgroup 
                   subgroup_imp_subset)

theorem factorgroup_is_group: "H <| G ==> (G Mod H) \<in> Group"
apply (frule normal_imp_coset) 
apply (simp add: FactGroup_def) 
apply (rule group.intro)
 apply (rule semigroup.intro) 
  apply (simp add: restrictI coset.setsum_closed) 
 apply (simp add: coset.setsum_closed coset.setrcos_assoc)  
apply (rule group_axioms.intro) 
   apply (simp add: restrictI setminus_closed) 
  apply (simp add: normal_imp_subgroup subgroup_in_rcosets) 
 apply (simp add: setminus_closed coset.setrcos_minus_sum_eq) 
apply (simp add: normal_imp_subgroup subgroup_in_rcosets coset.setrcos_sum_eq)
done


end
