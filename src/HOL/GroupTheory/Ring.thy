(*  Title:      HOL/GroupTheory/Ring
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson

*)

header{*Ring Theory*}

theory Ring = Bij + Coset:


subsection{*Definition of a Ring*}

record 'a ring  = "'a group" +
  prod :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"    (infixl "\<cdot>\<index>" 70)

record 'a unit_ring  = "'a ring" +
  one :: 'a    ("\<one>\<index>")


text{*Abbrevations for the left and right distributive laws*}
constdefs
  distrib_l :: "['a set, ['a, 'a] => 'a, ['a, 'a] => 'a] => bool"
    "distrib_l A f g ==
       (\<forall>x \<in> A. \<forall>y \<in> A. \<forall>z \<in> A. (f x (g y z) = g (f x y) (f x z)))"

  distrib_r       :: "['a set, ['a, 'a] => 'a, ['a, 'a] => 'a] => bool"
    "distrib_r A f g == 
       (\<forall>x \<in> A. \<forall>y \<in> A. \<forall>z \<in> A. (f (g y z) x = g (f y x) (f z x)))"


locale ring = abelian_group R +
  assumes prod_funcset: "prod R \<in> carrier R \<rightarrow> carrier R \<rightarrow> carrier R"
      and prod_assoc:   
            "[|x \<in> carrier R; y \<in> carrier R; z \<in> carrier R|] 
             ==> (x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
      and left:  "distrib_l (carrier R) (prod R) (sum R)"
      and right: "distrib_r (carrier R) (prod R) (sum R)"

constdefs
  Ring :: "('a,'b) ring_scheme set"
   "Ring == Collect ring"


lemma ring_is_abelian_group: "ring(R) ==> abelian_group(R)"
by (simp add: ring_def abelian_group_def)

text{*Construction of a ring from a semigroup and an Abelian group*}
lemma ringI:
     "[|abelian_group R; 
        semigroup(|carrier = carrier R, sum = prod R|);
        distrib_l (carrier R) (prod R) (sum R);
        distrib_r (carrier R) (prod R) (sum R)|] ==> ring R"
by (simp add: abelian_group_def ring_def ring_axioms_def semigroup_def) 

lemma (in ring) prod_closed [simp]:
     "[| x \<in> carrier R; y \<in> carrier R |] ==>  x \<cdot> y \<in> carrier R"
apply (insert prod_funcset) 
apply (blast dest: funcset_mem) 
done

declare ring.prod_closed [simp]

lemma (in ring) sum_closed:
     "[| x \<in> carrier R; y \<in> carrier R |] ==>  x \<oplus> y \<in> carrier R"
by simp 

declare ring.sum_closed [simp]

lemma (in ring) distrib_left:
     "[|x \<in> carrier R; y \<in> carrier R; z \<in> carrier R|]  
      ==> x \<cdot> (y \<oplus> z) = (x \<cdot> y) \<oplus> (x \<cdot> z)"
apply (insert left) 
apply (simp add: distrib_l_def)
done

lemma (in ring) distrib_right:
     "[|x \<in> carrier R; y \<in> carrier R; z \<in> carrier R|]  
      ==> (y \<oplus> z) \<cdot> x = (y \<cdot> x) \<oplus> (z \<cdot> x)"
apply (insert right) 
apply (simp add: distrib_r_def)
done

lemma (in ring) prod_zero_left: "x \<in> carrier R ==> \<zero> \<cdot> x = \<zero>"
by (simp add: idempotent_imp_zero distrib_right [symmetric])

lemma (in ring) prod_zero_right: "x \<in> carrier R ==> x \<cdot> \<zero> = \<zero>"
by (simp add: idempotent_imp_zero distrib_left [symmetric])

lemma (in ring) prod_minus_left:
     "[|x \<in> carrier R; y \<in> carrier R|]  
      ==> (\<ominus>x) \<cdot> y = \<ominus> (x \<cdot> y)"
by (simp add: minus_unique prod_zero_left distrib_right [symmetric]) 

lemma (in ring) prod_minus_right:
     "[|x \<in> carrier R; y \<in> carrier R|]  
      ==> x \<cdot> (\<ominus>y) = \<ominus> (x \<cdot> y)"
by (simp add: minus_unique prod_zero_right distrib_left [symmetric]) 


subsection {*Example: The Ring of Integers*}

constdefs
 integers :: "int ring"
  "integers == (|carrier = UNIV, 
                 sum = op +,
                 gminus = (%x. -x),
                 zero = 0::int,
                 prod = op *|)"

theorem ring_integers: "ring (integers)"
by (simp add: integers_def ring_def ring_axioms_def 
              distrib_l_def distrib_r_def 
              zadd_zmult_distrib zadd_zmult_distrib2 
              abelian_group_axioms_def group_axioms_def semigroup_def) 


subsection {*Ring Homomorphisms*}

constdefs
 ring_hom :: "[('a,'c)ring_scheme, ('b,'d)ring_scheme] => ('a => 'b)set"
  "ring_hom R R' ==
   {h. h \<in> carrier R -> carrier R' & 
       (\<forall>x \<in> carrier R. \<forall>y \<in> carrier R. h(sum R x y) = sum R' (h x) (h y)) &
       (\<forall>x \<in> carrier R. \<forall>y \<in> carrier R. h(prod R x y) = prod R' (h x) (h y))}"

 ring_auto :: "('a,'b)ring_scheme => ('a => 'a)set"
  "ring_auto R == ring_hom R R \<inter> Bij(carrier R)"

  RingAutoGroup :: "[('a,'c) ring_scheme] => ('a=>'a) group"
  "RingAutoGroup R == BijGroup (carrier R) (|carrier := ring_auto R |)"


lemma ring_hom_subset_hom: "ring_hom R R' <= hom R R'"
by (force simp add: ring_hom_def hom_def)

subsection{*The Ring Automorphisms From a Group*}

lemma id_in_ring_auto: "ring R ==> (%x: carrier R. x) \<in> ring_auto R"
by (simp add: ring_auto_def ring_hom_def restrictI ring.axioms id_Bij) 

lemma restrict_Inv_ring_hom:
      "[|ring R; h \<in> ring_hom R R; h \<in> Bij (carrier R)|]
       ==> restrict (Inv (carrier R) h) (carrier R) \<in> ring_hom R R"
by (simp add: ring.axioms group.axioms 
              ring_hom_def Bij_Inv_mem restrictI 
              semigroup.sum_funcset ring.prod_funcset Bij_Inv_lemma)

text{*Ring automorphisms are a subgroup of the group of bijections over the 
   ring's carrier, and thus a group*}
lemma subgroup_ring_auto:
      "ring R ==> subgroup (ring_auto R) (BijGroup (carrier R))"
apply (rule group.subgroupI) 
    apply (rule group_BijGroup) 
   apply (force simp add: ring_auto_def BijGroup_def) 
  apply (blast dest: id_in_ring_auto) 
 apply (simp add: ring_auto_def BijGroup_def restrict_Inv_Bij
                  restrict_Inv_ring_hom) 
apply (simp add: ring_auto_def BijGroup_def compose_Bij)
apply (simp add: ring_hom_def compose_def Pi_def)
done

lemma ring_auto: "ring R ==> group (RingAutoGroup R)"
apply (drule subgroup_ring_auto) 
apply (simp add: subgroup_def RingAutoGroup_def) 
done


subsection{*A Locale for a Pair of Rings and a Homomorphism*}

locale ring_homomorphism = ring R + ring R' +
  fixes h
  assumes homh: "h \<in> ring_hom R R'"

lemma ring_hom_sum:
     "[|h \<in> ring_hom R R'; x \<in> carrier R; y \<in> carrier R|] 
      ==> h(sum R x y) = sum R' (h x) (h y)"
by (simp add: ring_hom_def) 

lemma ring_hom_prod:
     "[|h \<in> ring_hom R R'; x \<in> carrier R; y \<in> carrier R|] 
      ==> h(prod R x y) = prod R' (h x) (h y)"
by (simp add: ring_hom_def) 

lemma ring_hom_closed:
     "[|h \<in> ring_hom G G'; x \<in> carrier G|] ==> h x \<in> carrier G'"
by (auto simp add: ring_hom_def funcset_mem)

lemma (in ring_homomorphism) ring_hom_sum [simp]:
     "[|x \<in> carrier R; y \<in> carrier R|] ==> h (x \<oplus>\<^sub>1 y) = (h x) \<oplus>\<^sub>2 (h y)"
by (simp add: ring_hom_sum [OF homh])

lemma (in ring_homomorphism) ring_hom_prod [simp]:
     "[|x \<in> carrier R; y \<in> carrier R|] ==> h (x \<cdot>\<^sub>1 y) = (h x) \<cdot>\<^sub>2 (h y)"
by (simp add: ring_hom_prod [OF homh])

lemma (in ring_homomorphism) group_homomorphism: "group_homomorphism R R' h"
by (simp add: group_homomorphism_def group_homomorphism_axioms_def
              prems homh ring_hom_subset_hom [THEN subsetD])

lemma (in ring_homomorphism) hom_zero_closed [simp]: "h \<zero>\<^sub>1 \<in> carrier R'"
by (simp add: ring_hom_closed [OF homh]) 

lemma (in ring_homomorphism) hom_zero [simp]: "h \<zero>\<^sub>1 = \<zero>\<^sub>2"
by (rule group_homomorphism.hom_zero [OF group_homomorphism]) 

lemma (in ring_homomorphism) hom_minus_closed [simp]:
     "x \<in> carrier R ==> h (\<ominus>x) \<in> carrier R'"
by (rule group_homomorphism.hom_minus_closed [OF group_homomorphism]) 

lemma (in ring_homomorphism) hom_minus [simp]:
     "x \<in> carrier R ==> h (\<ominus>\<^sub>1 x) = \<ominus>\<^sub>2 (h x)"
by (rule group_homomorphism.hom_minus [OF group_homomorphism]) 


text{*Needed because the standard theorem @{text "ring_homomorphism.intro"} 
is unnatural.*}
lemma ring_homomorphismI:
    "[|ring R; ring R'; h \<in> ring_hom R R'|] ==> ring_homomorphism R R' h"
by (simp add: ring_def ring_homomorphism_def ring_homomorphism_axioms_def)

end
