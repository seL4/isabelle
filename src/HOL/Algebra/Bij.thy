(*  Title:      HOL/Algebra/Bij.thy
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
*)

header {* Bijections of a Set, Permutation Groups, Automorphism Groups *}

theory Bij = Group:

constdefs
  Bij :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) set"
    --{*Only extensional functions, since otherwise we get too many.*}
  "Bij S \<equiv> extensional S \<inter> {f. bij_betw f S S}"

  BijGroup :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) monoid"
  "BijGroup S \<equiv>
    \<lparr>carrier = Bij S,
     mult = \<lambda>g \<in> Bij S. \<lambda>f \<in> Bij S. compose S g f,
     one = \<lambda>x \<in> S. x\<rparr>"


declare Id_compose [simp] compose_Id [simp]

lemma Bij_imp_extensional: "f \<in> Bij S \<Longrightarrow> f \<in> extensional S"
  by (simp add: Bij_def)

lemma Bij_imp_funcset: "f \<in> Bij S \<Longrightarrow> f \<in> S \<rightarrow> S"
  by (auto simp add: Bij_def bij_betw_imp_funcset)


subsection {*Bijections Form a Group *}

lemma restrict_Inv_Bij: "f \<in> Bij S \<Longrightarrow> (\<lambda>x \<in> S. (Inv S f) x) \<in> Bij S"
  by (simp add: Bij_def bij_betw_Inv)

lemma id_Bij: "(\<lambda>x\<in>S. x) \<in> Bij S "
  by (auto simp add: Bij_def bij_betw_def inj_on_def)

lemma compose_Bij: "\<lbrakk>x \<in> Bij S; y \<in> Bij S\<rbrakk> \<Longrightarrow> compose S x y \<in> Bij S"
  by (auto simp add: Bij_def bij_betw_compose) 

lemma Bij_compose_restrict_eq:
     "f \<in> Bij S \<Longrightarrow> compose S (restrict (Inv S f) S) f = (\<lambda>x\<in>S. x)"
  by (simp add: Bij_def compose_Inv_id)

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

lemma Bij_Inv_mem: "\<lbrakk> f \<in> Bij S;  x \<in> S\<rbrakk> \<Longrightarrow> Inv S f x \<in> S"
by (simp add: Bij_def bij_betw_def Inv_mem)

lemma Bij_Inv_lemma:
 assumes eq: "\<And>x y. \<lbrakk>x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> h(g x y) = g (h x) (h y)"
 shows "\<lbrakk>h \<in> Bij S;  g \<in> S \<rightarrow> S \<rightarrow> S;  x \<in> S;  y \<in> S\<rbrakk>
        \<Longrightarrow> Inv S h (g x y) = g (Inv S h x) (Inv S h y)"
apply (simp add: Bij_def bij_betw_def)
apply (subgoal_tac "\<exists>x'\<in>S. \<exists>y'\<in>S. x = h x' & y = h y'", clarify)
 apply (simp add: eq [symmetric] Inv_f_f funcset_mem [THEN funcset_mem], blast)
done


constdefs
  auto :: "('a, 'b) monoid_scheme \<Rightarrow> ('a \<Rightarrow> 'a) set"
  "auto G \<equiv> hom G G \<inter> Bij (carrier G)"

  AutoGroup :: "('a, 'c) monoid_scheme \<Rightarrow> ('a \<Rightarrow> 'a) monoid"
  "AutoGroup G \<equiv> BijGroup (carrier G) \<lparr>carrier := auto G\<rparr>"

lemma (in group) id_in_auto: "(\<lambda>x \<in> carrier G. x) \<in> auto G"
  by (simp add: auto_def hom_def restrictI group.axioms id_Bij)

lemma (in group) mult_funcset: "mult G \<in> carrier G \<rightarrow> carrier G \<rightarrow> carrier G"
  by (simp add:  Pi_I group.axioms)

lemma (in group) restrict_Inv_hom:
      "\<lbrakk>h \<in> hom G G; h \<in> Bij (carrier G)\<rbrakk>
       \<Longrightarrow> restrict (Inv (carrier G) h) (carrier G) \<in> hom G G"
  by (simp add: hom_def Bij_Inv_mem restrictI mult_funcset
                group.axioms Bij_Inv_lemma)

lemma inv_BijGroup:
     "f \<in> Bij S \<Longrightarrow> m_inv (BijGroup S) f = (\<lambda>x \<in> S. (Inv S f) x)"
apply (rule group.inv_equality)
apply (rule group_BijGroup)
apply (simp_all add: BijGroup_def restrict_Inv_Bij Bij_compose_restrict_eq)
done

lemma (in group) subgroup_auto:
      "subgroup (auto G) (BijGroup (carrier G))"
proof (rule subgroup.intro)
  show "auto G \<subseteq> carrier (BijGroup (carrier G))"
    by (force simp add: auto_def BijGroup_def)
next
  fix x y
  assume "x \<in> auto G" "y \<in> auto G" 
  thus "x \<otimes>\<^bsub>BijGroup (carrier G)\<^esub> y \<in> auto G"
    by (force simp add: BijGroup_def is_group auto_def Bij_imp_funcset 
                        group.hom_compose compose_Bij)
next
  show "\<one>\<^bsub>BijGroup (carrier G)\<^esub> \<in> auto G" by (simp add:  BijGroup_def id_in_auto)
next
  fix x 
  assume "x \<in> auto G" 
  thus "inv\<^bsub>BijGroup (carrier G)\<^esub> x \<in> auto G"
    by (simp del: restrict_apply
             add: inv_BijGroup auto_def restrict_Inv_Bij restrict_Inv_hom)
qed

theorem (in group) AutoGroup: "group (AutoGroup G)"
by (simp add: AutoGroup_def subgroup.subgroup_is_group subgroup_auto 
              group_BijGroup)

end
