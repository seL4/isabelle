(*  Title:      HOL/GroupTheory/Group
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
*)

header{*Group Theory Using Locales*}

theory Group = FuncSet:

subsection{*Semigroups*}

record 'a semigroup =
  carrier :: "'a set"    
  sum :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"    (infixl "\<oplus>\<index>" 65)

locale semigroup =
  fixes S    (structure)
  assumes sum_funcset: "sum S \<in> carrier S \<rightarrow> carrier S \<rightarrow> carrier S"
      and sum_assoc:   
            "[|x \<in> carrier S; y \<in> carrier S; z \<in> carrier S|] 
             ==> (x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"

constdefs
  order     :: "(('a,'b) semigroup_scheme) => nat"
   "order(S) == card(carrier S)"


(*Overloading is impossible because of the way record types are represented*)
constdefs
  subsemigroup  :: "['a set, ('a,'b) semigroup_scheme] => bool"
   "subsemigroup H G == 
	H <= carrier G & 
	semigroup G &
        semigroup (G(|carrier:=H|))"

(*a characterization of subsemigroups *)
lemma (in semigroup) subsemigroupI:
     "[| H <= carrier S; 
         !!a b. [|a \<in> H; b \<in> H|] ==> a \<oplus> b \<in> H |] 
      ==> subsemigroup H S"
apply (insert prems) 
apply (simp add: semigroup_def subsemigroup_def, clarify) 
apply (blast intro: funcsetI) 
done


subsection{*Groups*}

record 'a group = "'a semigroup" +
  gminus :: "'a \<Rightarrow> 'a"    ("(\<ominus>\<index>_)" [81] 80)
  zero :: 'a    ("\<zero>\<index>")

locale group = semigroup G +
  assumes minus_funcset: "gminus G \<in> carrier G \<rightarrow> carrier G"
      and zero_closed [iff]: 
            "zero G \<in> carrier G"
      and left_minus [simp]: 
            "x \<in> carrier G ==> (\<ominus>x) \<oplus> x = \<zero>"
      and left_zero [simp]:
            "x \<in> carrier G ==> \<zero> \<oplus> x = x"


constdefs
  Group :: "('a,'b) group_scheme set"
   "Group == Collect group"

lemma [simp]: "(G \<in> Group) = (group G)"
by (simp add: Group_def) 

lemma "group G ==> semigroup G"
by (simp add: group_def semigroup_def) 


locale abelian_group = group +
  assumes sum_commute: "[|x \<in> carrier G; y \<in> carrier G|] ==> x \<oplus> y = y \<oplus> x"

lemma abelian_group_iff:
     "abelian_group G = 
      (group G & (\<forall>x \<in> carrier G. \<forall>y \<in> carrier G. sum G x y = sum G y x))"
by (force simp add: abelian_group_axioms_def abelian_group_def group_def) 


subsection{*Basic Group Theory Theorems*}

lemma (in semigroup) sum_closed [simp]: 
     "[|x \<in> carrier S; y \<in> carrier S|] ==> (x \<oplus> y) \<in> carrier S"
apply (insert sum_funcset) 
apply (blast dest: funcset_mem) 
done

lemma (in group) minus_closed [simp]: 
     "x \<in> carrier G ==> (\<ominus>x) \<in> carrier G"
apply (insert minus_funcset) 
apply (blast dest: funcset_mem) 
done

lemma (in group) left_cancellation:
  assumes "x \<oplus> y  =  x \<oplus> z"
          "x \<in> carrier G" "y \<in> carrier G" "z \<in> carrier G" 
  shows "y = z"
proof -
  have "((\<ominus>x) \<oplus> x) \<oplus> y = ((\<ominus>x) \<oplus> x) \<oplus> z" 
        by (simp only: prems minus_closed sum_assoc) 
  thus ?thesis by (simp add: prems) 
qed

lemma (in group) left_cancellation_iff [simp]:
     "[| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |]  
      ==> (x \<oplus> y  =  x \<oplus> z) = (y = z)"
by (blast intro: left_cancellation)


subsection{*The Other Directions of Basic Lemmas*}

lemma (in group) right_zero [simp]: "x \<in> carrier G ==> x \<oplus> \<zero> = x"
apply (rule left_cancellation [of "(\<ominus>x)"])
apply (auto simp add: sum_assoc [symmetric])
done

lemma (in group) idempotent_imp_zero: "[| x \<in> carrier G; x \<oplus> x = x |] ==> x=\<zero>"
by (rule left_cancellation [of x], auto)

lemma (in group) right_minus [simp]: "x \<in> carrier G ==> x \<oplus> (\<ominus>x) = \<zero>"
apply (rule idempotent_imp_zero)
apply (simp_all add: sum_assoc [symmetric])
apply (simp add: sum_assoc)
done

lemma (in group) minus_unique:
     "[| x \<in> carrier G; y \<in> carrier G; x \<oplus> y = \<zero> |] ==> y = (\<ominus>x)"
apply (rule left_cancellation [of x], auto)
done

lemma (in group) minus_minus [simp]:
     "x \<in> carrier G ==> \<ominus>(\<ominus>x) = x"
apply (rule left_cancellation [of "(\<ominus>x)"])
apply auto
done

lemma (in group) minus_sum:
     "[| x \<in> carrier G; y \<in> carrier G |] ==> \<ominus>(x \<oplus> y) = (\<ominus>y) \<oplus> (\<ominus>x)"
apply (rule minus_unique [symmetric])
apply (simp_all add: sum_assoc [symmetric])
apply (simp add: sum_assoc) 
done

lemma (in group) right_cancellation:
     "[| y \<oplus> x =  z \<oplus> x;   
         x \<in> carrier G; y \<in> carrier G; z \<in> carrier G|] ==> y = z"
apply (drule arg_cong [of concl: "%z. z \<oplus> (\<ominus>x)"])
apply (simp add: sum_assoc)
done

lemma (in group) right_cancellation_iff [simp]:
     "[| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |]  
      ==> (y \<oplus> x =  z \<oplus> x) = (y = z)"
by (blast intro: right_cancellation)


subsection{*The Subgroup Relation*}

constdefs  
  subgroup  :: "['a set, ('a,'b) group_scheme] => bool"
   "subgroup H G == 
	H <= carrier G & 
	group G &
        group (G(|carrier:=H|))";


text{*Since @{term H} is nonempty, it contains some element @{term x}.  Since
it's closed under inverse, it contains @{text "(\<ominus>x)"}.  Since
it's closed under sum, it contains @{text "x \<oplus> (\<ominus>x) = \<zero>"}.
How impressive that the proof is automatic!*}
lemma (in group) zero_in_subset:
     "[| H <= carrier G; H \<noteq> {}; \<forall>a \<in> H. (\<ominus>a) \<in> H; \<forall>a\<in>H. \<forall>b\<in>H. a \<oplus> b \<in> H|]
      ==> \<zero> \<in> H"
by force

text{*A characterization of subgroups*}
lemma (in group) subgroupI:
     "[| H <= carrier G;  H \<noteq> {};  
         !!a. a \<in> H ==> (\<ominus>a) \<in> H; 
         !!a b. [|a \<in> H; b \<in> H|] ==> a \<oplus> b \<in> H |] 
      ==> subgroup H G"
apply (insert prems) 
apply (simp add: group_def subgroup_def)
apply (simp add: semigroup_def group_axioms_def, clarify) 
apply (intro conjI ballI)
apply (simp_all add: funcsetI subsetD [of H "carrier G"])
apply (blast intro: zero_in_subset)  
done


lemma subgroup_imp_subset: "subgroup H G  ==> H <= carrier G"
by (simp add: subgroup_def)

lemma (in group) subgroup_sum_closed:
     "[| subgroup H G; x \<in> H; y \<in> H |] ==> x \<oplus> y \<in> H"
by (simp add: subgroup_def group_def semigroup_def Pi_def) 

lemma (in group) subgroup_minus_closed:
     "[| subgroup H G; x \<in> H |] ==> (\<ominus>x) \<in> H"
by (simp add: subgroup_def group_def group_axioms_def Pi_def) 

lemma (in group) subgroup_zero_closed: "subgroup H G ==> \<zero> \<in> H"
by (simp add: subgroup_def group_def group_axioms_def) 

text{*Global declarations, in force outside the locale*}
declare semigroup.sum_closed [simp]

declare group.zero_closed [iff]
    and group.minus_closed [simp]
    and group.left_minus [simp]
    and group.left_zero [simp]
    and group.right_minus [simp]
    and group.right_zero [simp]
    and group.minus_minus [simp]


lemma subgroup_imp_group: "subgroup H G ==> group G"
by (simp add: subgroup_def) 

lemma subgroup_nonempty: "~ subgroup {} G"
by (blast dest: subgroup_imp_group group.subgroup_zero_closed)

lemma subgroup_card_positive:
     "[| finite(carrier G); subgroup H G |] ==> 0 < card(H)"
apply (subgoal_tac "finite H")
 prefer 2 apply (blast intro: finite_subset dest: subgroup_imp_subset)
apply (rule ccontr)
apply (simp add: card_0_eq subgroup_nonempty) 
done

subsection{*Direct Product of Two Groups*}

text{*We want to overload product for all algebraic structures.  But it is not
easy.  All of them are instances of the same type, namely @{text
carrier_field_type}, which the record declaration generates automatically.
Overloading requires distinct types.*}

constdefs 
  ProdGroup :: "[('a,'c) group_scheme, ('b,'d) group_scheme] => ('a*'b) group"
            (infixr "'(*')" 80)
  "G (*) G' ==
    (| carrier = carrier G \<times> carrier G',
       sum = (%(x, x') (y, y'). (sum G x y, sum G' x' y')),
       gminus = (%(x, y). (gminus G x, gminus G' y)),
       zero = (zero G, zero G') |)"

syntax (xsymbols)
  ProdGroup :: "[('a,'c) group_scheme, ('b,'d) group_scheme] => ('a*'b) group"
            (infixr "\<otimes>" 80)


lemma P_carrier: "(carrier (G\<otimes>G')) = ((carrier G) \<times> (carrier G'))"
by (simp add: ProdGroup_def)

lemma P_sum: "sum (G\<otimes>G') = (%(x, x') (y, y'). (sum G x y, sum G' x' y'))"
by (simp add: ProdGroup_def)

lemma P_minus: "(gminus (G\<otimes>G')) = (%(x, y). (gminus G x, gminus G' y))"
by (simp add: ProdGroup_def)

lemma P_zero: "zero (G\<otimes>G') = (zero G, zero G')"
by (simp add: ProdGroup_def)

lemma P_sum_funcset:
     "[|semigroup G; semigroup G'|] ==>
      sum(G\<otimes>G') : carrier(G\<otimes>G') \<rightarrow> carrier(G\<otimes>G') \<rightarrow> carrier(G\<otimes>G')"
by (auto intro!: funcsetI 
         simp add: semigroup.sum_closed P_sum P_carrier)

lemma P_minus_funcset: 
     "[|group G; group G'|] ==>
      gminus(G\<otimes>G') : carrier(G\<otimes>G') \<rightarrow> carrier(G\<otimes>G')"
by (auto intro!: funcsetI 
         simp add: group_def group.minus_closed P_minus P_carrier)

theorem ProdGroup_is_group: "[|group G; group G'|] ==> group (G\<otimes>G')"
apply (rule group.intro)
 apply (simp add: group_def)  
 apply (rule semigroup.intro) 
  apply (simp add: group_def P_sum_funcset)  
 apply (force simp add: ProdGroup_def semigroup.sum_assoc)
apply (rule group_axioms.intro) 
   apply (simp add: P_minus_funcset)  
  apply (simp add: ProdGroup_def group.zero_closed) 
 apply (force simp add: ProdGroup_def group.left_minus) 
apply (force simp add: ProdGroup_def group.left_zero) 
done

lemma ProdGroup_arity: "ProdGroup : Group \<rightarrow> Group \<rightarrow> Group"
by (auto intro!: funcsetI ProdGroup_is_group)

subsection{*Homomorphisms on Groups and Semigroups*}

constdefs
  hom :: "[('a,'c)semigroup_scheme, ('b,'d)semigroup_scheme] => ('a => 'b)set"
   "hom S S' ==
     {h. h \<in> carrier S -> carrier S' & 
	 (\<forall>x \<in> carrier S. \<forall>y \<in> carrier S. h(sum S x y) = sum S' (h x) (h y))}"

lemma hom_semigroup:
     "semigroup S ==> semigroup (|carrier = hom S S, sum = (%h g. h o g) |)"
apply (simp add: semigroup_def o_assoc) 
apply (simp add: Pi_def hom_def) 
done

lemma hom_sum:
     "[|h \<in> hom S S'; x \<in> carrier S; y \<in> carrier S|] 
      ==> h(sum S x y) = sum S' (h x) (h y)"
by (simp add: hom_def) 

lemma hom_closed:
     "[|h \<in> hom G G'; x \<in> carrier G|] ==> h x \<in> carrier G'"
by (auto simp add: hom_def funcset_mem) 

lemma hom_zero_closed [simp]:
     "[|h \<in> hom G G'; group G|] ==> h (zero G) \<in> carrier G'"
by (auto simp add: hom_closed) 

text{*Or just @{text "group_hom.hom_zero [OF group_homI]"}*}
lemma hom_zero [simp]:
     "[|h \<in> hom G G'; group G; group G'|] ==> h (zero G) = zero G'"
by (simp add: group.idempotent_imp_zero hom_sum [of h, symmetric]) 

lemma hom_minus_closed [simp]:
     "[|h \<in> hom G G'; x \<in> carrier G; group G|] 
      ==> h (gminus G x) \<in> carrier G'"
by (simp add: hom_closed) 

text{*Or just @{text "group_hom.hom_minus [OF group_homI]"}*}
lemma hom_minus [simp]:
     "[|h \<in> hom G G'; x \<in> carrier G; group G; group G'|] 
      ==> h (gminus G x) = gminus G' (h x)"
by (simp add: group.minus_unique hom_closed hom_sum [of h, symmetric])


text{*This locale uses the subscript notation mentioned by Wenzel in 
@{text "HOL/ex/Locales.thy"}.  We fix two groups and a homomorphism between 
them.  Then we prove theorems similar to those just above.*}

locale group_homomorphism = group G + group G' +
  fixes h
  assumes homh: "h \<in> hom G G'"

lemma (in group_homomorphism) hom_sum [simp]:
     "[|x \<in> carrier G; y \<in> carrier G|] ==> h (x \<oplus>\<^sub>1 y) = (h x) \<oplus>\<^sub>2 (h y)"
by (simp add: hom_sum [OF homh])

lemma (in group_homomorphism) hom_zero_closed [simp]: "h \<zero>\<^sub>1 \<in> carrier G'"
by (simp add: hom_closed [OF homh]) 

lemma (in group_homomorphism) hom_zero [simp]: "h \<zero>\<^sub>1 = \<zero>\<^sub>2"
by (simp add: idempotent_imp_zero hom_sum [symmetric]) 

lemma (in group_homomorphism) hom_minus_closed [simp]:
     "x \<in> carrier G ==> h (\<ominus>x) \<in> carrier G'"
by (simp add: hom_closed [OF homh]) 

lemma (in group_homomorphism) hom_minus [simp]:
     "x \<in> carrier G ==> h (\<ominus>\<^sub>1 x) = \<ominus>\<^sub>2 (h x)"
by (simp add: minus_unique hom_closed [OF homh] hom_sum [symmetric])

text{*Necessary because the standard theorem
    @{text "group_homomorphism.intro"} is unnatural.*}
lemma group_homomorphismI:
    "[|group G; group G'; h \<in> hom G G'|] ==> group_homomorphism G G' h"
by (simp add: group_def group_homomorphism_def group_homomorphism_axioms_def)

end
 
