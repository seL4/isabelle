(*  Title:      HOL/Algebra/Bij
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
*)


header{*Bijections of a Set, Permutation Groups, Automorphism Groups*} 

theory Bij = Group:

constdefs
  Bij :: "'a set => (('a => 'a)set)" 
    --{*Only extensional functions, since otherwise we get too many.*}
    "Bij S == extensional S \<inter> {f. f`S = S & inj_on f S}"

   BijGroup ::  "'a set => (('a => 'a) monoid)"
   "BijGroup S == (| carrier = Bij S, 
		     mult  = %g: Bij S. %f: Bij S. compose S g f,
		     one = %x: S. x |)"


declare Id_compose [simp] compose_Id [simp]

lemma Bij_imp_extensional: "f \<in> Bij S ==> f \<in> extensional S"
by (simp add: Bij_def)

lemma Bij_imp_funcset: "f \<in> Bij S ==> f \<in> S -> S"
by (auto simp add: Bij_def Pi_def)

lemma Bij_imp_apply: "f \<in> Bij S ==> f ` S = S"
by (simp add: Bij_def)

lemma Bij_imp_inj_on: "f \<in> Bij S ==> inj_on f S"
by (simp add: Bij_def)

lemma BijI: "[| f \<in> extensional(S); f`S = S; inj_on f S |] ==> f \<in> Bij S"
by (simp add: Bij_def)


subsection{*Bijections Form a Group*}

lemma restrict_Inv_Bij: "f \<in> Bij S ==> (%x:S. (Inv S f) x) \<in> Bij S"
apply (simp add: Bij_def)
apply (intro conjI)
txt{*Proving @{term "restrict (Inv S f) S ` S = S"}*}
 apply (rule equalityI)
  apply (force simp add: Inv_mem) --{*first inclusion*}
 apply (rule subsetI)   --{*second inclusion*}
 apply (rule_tac x = "f x" in image_eqI)
  apply (force intro:  simp add: Inv_f_f, blast)
txt{*Remaining goal: @{term "inj_on (restrict (Inv S f) S) S"}*}
apply (rule inj_onI)
apply (auto elim: Inv_injective)
done

lemma id_Bij: "(\<lambda>x\<in>S. x) \<in> Bij S "
apply (rule BijI)
apply (auto simp add: inj_on_def)
done

lemma compose_Bij: "[| x \<in> Bij S; y \<in> Bij S|] ==> compose S x y \<in> Bij S"
apply (rule BijI)
  apply (simp add: compose_extensional) 
 apply (blast del: equalityI
              intro: surj_compose dest: Bij_imp_apply Bij_imp_inj_on)
apply (blast intro: inj_on_compose dest: Bij_imp_apply Bij_imp_inj_on)
done

lemma Bij_compose_restrict_eq:
     "f \<in> Bij S ==> compose S (restrict (Inv S f) S) f = (\<lambda>x\<in>S. x)"
apply (rule compose_Inv_id)
 apply (simp add: Bij_imp_inj_on)
apply (simp add: Bij_imp_apply) 
done

theorem group_BijGroup: "group (BijGroup S)"
apply (simp add: BijGroup_def) 
apply (rule groupI)
    apply (simp add: compose_Bij)
   apply (simp add: id_Bij)
  apply (simp add: compose_Bij)
  apply (blast intro: compose_assoc [symmetric] Bij_imp_funcset)
 apply (simp add: id_Bij Bij_imp_funcset Bij_imp_extensional, simp)
apply (blast intro: Bij_compose_restrict_eq restrict_Inv_Bij) 
done


subsection{*Automorphisms Form a Group*}

lemma Bij_Inv_mem: "[|  f \<in> Bij S;  x : S |] ==> Inv S f x : S"
by (simp add: Bij_def Inv_mem) 

lemma Bij_Inv_lemma:
 assumes eq: "!!x y. [|x \<in> S; y \<in> S|] ==> h(g x y) = g (h x) (h y)"
 shows "[| h \<in> Bij S;  g \<in> S \<rightarrow> S \<rightarrow> S;  x \<in> S;  y \<in> S |]        
        ==> Inv S h (g x y) = g (Inv S h x) (Inv S h y)"
apply (simp add: Bij_def) 
apply (subgoal_tac "EX x':S. EX y':S. x = h x' & y = h y'", clarify)
 apply (simp add: eq [symmetric] Inv_f_f funcset_mem [THEN funcset_mem], blast)
done

constdefs
 auto :: "('a,'b) monoid_scheme => ('a => 'a)set"
  "auto G == hom G G \<inter> Bij (carrier G)"

  AutoGroup :: "[('a,'c) monoid_scheme] => ('a=>'a) monoid"
  "AutoGroup G == BijGroup (carrier G) (|carrier := auto G |)"

lemma id_in_auto: "group G ==> (%x: carrier G. x) \<in> auto G"
  by (simp add: auto_def hom_def restrictI group.axioms id_Bij) 

lemma mult_funcset: "group G ==> mult G \<in> carrier G -> carrier G -> carrier G"
  by (simp add:  Pi_I group.axioms)

lemma restrict_Inv_hom:
      "[|group G; h \<in> hom G G; h \<in> Bij (carrier G)|]
       ==> restrict (Inv (carrier G) h) (carrier G) \<in> hom G G"
  by (simp add: hom_def Bij_Inv_mem restrictI mult_funcset
                group.axioms Bij_Inv_lemma)

lemma inv_BijGroup:
     "f \<in> Bij S ==> m_inv (BijGroup S) f = (%x: S. (Inv S f) x)"
apply (rule group.inv_equality)
apply (rule group_BijGroup)
apply (simp_all add: BijGroup_def restrict_Inv_Bij Bij_compose_restrict_eq)  
done

lemma subgroup_auto:
      "group G ==> subgroup (auto G) (BijGroup (carrier G))"
apply (rule group.subgroupI) 
    apply (rule group_BijGroup) 
   apply (force simp add: auto_def BijGroup_def) 
  apply (blast intro: dest: id_in_auto) 
 apply (simp del: restrict_apply
	     add: inv_BijGroup auto_def restrict_Inv_Bij restrict_Inv_hom) 
apply (simp add: BijGroup_def auto_def Bij_imp_funcset compose_hom compose_Bij)
done

theorem AutoGroup: "group G ==> group (AutoGroup G)"
apply (simp add: AutoGroup_def) 
apply (rule Group.subgroup.groupI)
apply (erule subgroup_auto)  
apply (insert Bij.group_BijGroup [of "carrier G"]) 
apply (simp_all add: group_def) 
done

end

