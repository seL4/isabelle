(*  Title:      HOL/GroupTheory/Module
    ID:         $Id$
    Author:     Lawrence C Paulson

*)

header{*Modules*}

theory Module = Ring:

text{*The record includes all the group components (carrier, sum, gminus,
zero), adding the scalar product.*}
record ('a,'b) module  = "'a group" + 
  sprod :: "'b \<Rightarrow> 'a \<Rightarrow> 'a"   (infixl "\<star>\<index>" 70) 

text{*The locale assumes all the properties of a ring and an Abelian group,
adding laws relating them.*}
locale module = ring R + abelian_group M +
  assumes sprod_funcset: "sprod M \<in> carrier R \<rightarrow> carrier M \<rightarrow> carrier M"
      and sprod_assoc:   
            "[|r \<in> carrier R; s \<in> carrier R; a \<in> carrier M|] 
             ==> (r \<cdot>\<^sub>1 s) \<star>\<^sub>2 a = r \<star>\<^sub>2 (s \<star>\<^sub>2 a)"
      and sprod_distrib_left:
            "[|r \<in> carrier R; a \<in> carrier M; b \<in> carrier M|] 
             ==> r \<star>\<^sub>2 (a \<oplus>\<^sub>2 b) = (r \<star>\<^sub>2 a) \<oplus>\<^sub>2 (r \<star>\<^sub>2 b)"
      and sprod_distrib_right:
            "[|r \<in> carrier R; s \<in> carrier R; a \<in> carrier M|] 
             ==> (r \<oplus>\<^sub>1 s) \<star>\<^sub>2 a = (r \<star>\<^sub>2 a) \<oplus>\<^sub>2 (s \<star>\<^sub>2 a)"

lemma module_iff:
     "module R M = (ring R & abelian_group M & module_axioms R M)"
by (simp add: module_def ring_def abelian_group_def) 

text{*The sum and product in @{text R} are @{text "r \<oplus>\<^sub>1 s"} and @{text
"r \<cdot>\<^sub>1 s"}, respectively.  The sum in @{text M} is @{text "a \<oplus>\<^sub>2 b"}.*}


text{*We have to write the ring product as @{text "\<cdot>\<^sub>2"}. But if we
refer to the scalar product as @{text "\<cdot>\<^sub>1"} then syntactic ambiguities
arise.  This presumably happens because the subscript merely determines which
structure argument to insert, which happens after parsing.  Better to use a
different symbol such as @{text "\<star>"}*}

subsection {*Trivial Example: Every Ring is an R-Module Over Itself *}

constdefs
 triv_mod :: "('a,'b) ring_scheme => ('a,'a) module"
  "triv_mod R == (|carrier = carrier R,
                 sum = sum R,
                 gminus = gminus R,
                 zero = zero R, 
                 sprod = prod R|)"

theorem module_triv_mod: "ring R ==> module R (triv_mod R)"
apply (simp add: triv_mod_def module_iff module_axioms_def
                 ring_def ring_axioms_def abelian_group_def
                 distrib_l_def distrib_r_def semigroup_def group_axioms_def)
apply (simp add: abelian_group_axioms_def)
  --{*Combining the two simplifications causes looping!*}
done

end
