(*  Title:      HOLCF/TypedefPcpo.thy
    ID:         $Id$
    Author:     Brian Huffman
*)

header {* Subtypes of pcpos *}

theory TypedefPcpo
imports Adm
begin

subsection {* Proving a subtype is a partial order *}

text {*
  A subtype of a partial order is itself a partial order,
  if the ordering is defined in the standard way.
*}

theorem typedef_po:
fixes Abs :: "'a::po \<Rightarrow> 'b::sq_ord"
assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
shows "OFCLASS('b, po_class)"
 apply (intro_classes, unfold less)
   apply (rule refl_less)
  apply (subst type_definition.Rep_inject [OF type, symmetric])
  apply (rule antisym_less, assumption+)
 apply (rule trans_less, assumption+)
done


subsection {* Proving a subtype is complete *}

text {*
  A subtype of a cpo is itself a cpo if the ordering is
  defined in the standard way, and the defining subset
  is closed with respect to limits of chains.  A set is
  closed if and only if membership in the set is an
  admissible predicate.
*}

lemma chain_Rep:
assumes less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
shows "chain S \<Longrightarrow> chain (\<lambda>n. Rep (S n))"
by (rule chainI, drule chainE, unfold less)

lemma lub_Rep_in_A:
fixes Abs :: "'a::cpo \<Rightarrow> 'b::po"
assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
    and adm:  "adm (\<lambda>x. x \<in> A)"
shows "chain S \<Longrightarrow> (LUB n. Rep (S n)) \<in> A"
 apply (erule admD [OF adm chain_Rep [OF less], rule_format])
 apply (rule type_definition.Rep [OF type])
done

theorem typedef_is_lub:
fixes Abs :: "'a::cpo \<Rightarrow> 'b::po"
assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
    and adm: "adm (\<lambda>x. x \<in> A)"
shows "chain S \<Longrightarrow> range S <<| Abs (LUB n. Rep (S n))"
 apply (rule is_lubI)
  apply (rule ub_rangeI)
  apply (subst less)
  apply (subst type_definition.Abs_inverse [OF type])
   apply (erule lub_Rep_in_A [OF type less adm])
  apply (rule is_ub_thelub)
  apply (erule chain_Rep [OF less])
 apply (subst less)
 apply (subst type_definition.Abs_inverse [OF type])
  apply (erule lub_Rep_in_A [OF type less adm])
 apply (rule is_lub_thelub)
  apply (erule chain_Rep [OF less])
 apply (rule ub_rangeI)
 apply (drule ub_rangeD)
 apply (unfold less)
 apply assumption
done

theorem typedef_cpo:
fixes Abs :: "'a::cpo \<Rightarrow> 'b::po"
assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
    and adm: "adm (\<lambda>x. x \<in> A)"
shows "OFCLASS('b, cpo_class)"
 apply (intro_classes)
 apply (rule_tac x="Abs (LUB n. Rep (S n))" in exI)
 apply (erule typedef_is_lub [OF type less adm])
done


subsubsection {* Continuity of @{term Rep} and @{term Abs} *}

text {* For any sub-cpo, the @{term Rep} function is continuous. *}

theorem typedef_cont_Rep:
fixes Abs :: "'a::cpo \<Rightarrow> 'b::cpo"
assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
    and adm: "adm (\<lambda>x. x \<in> A)"
shows "cont Rep"
 apply (rule contI[rule_format])
 apply (simp only: typedef_is_lub [OF type less adm, THEN thelubI])
 apply (subst type_definition.Abs_inverse [OF type])
  apply (erule lub_Rep_in_A [OF type less adm])
 apply (rule thelubE [OF _ refl])
 apply (erule chain_Rep [OF less])
done

text {*
  For a sub-cpo, we can make the @{term Abs} function continuous
  only if we restrict its domain to the defining subset by
  composing it with another continuous function.
*}

theorem typedef_cont_Abs:
fixes Abs :: "'a::cpo \<Rightarrow> 'b::cpo"
fixes f :: "'c::cpo \<Rightarrow> 'a::cpo"
assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
    and adm: "adm (\<lambda>x. x \<in> A)"
    and f_in_A: "\<And>x. f x \<in> A"
    and cont_f: "cont f"
shows "cont (\<lambda>x. Abs (f x))"
 apply (rule contI[rule_format])
 apply (rule is_lubI)
  apply (rule ub_rangeI)
  apply (simp only: less type_definition.Abs_inverse [OF type f_in_A])
  apply (rule monofun_fun_arg [OF cont2mono [OF cont_f]])
  apply (erule is_ub_thelub)
 apply (simp only: less type_definition.Abs_inverse [OF type f_in_A])
 apply (simp only: contlubE[rule_format, OF cont2contlub [OF cont_f]])
 apply (rule is_lub_thelub)
  apply (erule ch2ch_monofun [OF cont2mono [OF cont_f]])
 apply (rule ub_rangeI)
 apply (drule_tac i=i in ub_rangeD)
 apply (simp only: less type_definition.Abs_inverse [OF type f_in_A])
done


subsection {* Proving a typedef is pointed *}

text {*
  A subtype of a cpo has a least element if and only if
  the defining subset has a least element.
*}

theorem typedef_pcpo:
fixes Abs :: "'a::cpo \<Rightarrow> 'b::cpo"
assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
    and z_in_A: "z \<in> A"
    and z_least: "\<And>x. x \<in> A \<Longrightarrow> z \<sqsubseteq> x"
shows "OFCLASS('b, pcpo_class)"
 apply (intro_classes)
 apply (rule_tac x="Abs z" in exI, rule allI)
 apply (unfold less)
 apply (subst type_definition.Abs_inverse [OF type z_in_A])
 apply (rule z_least [OF type_definition.Rep [OF type]])
done

text {*
  As a special case, a subtype of a pcpo has a least element
  if the defining subset contains @{term \<bottom>}.
*}

theorem typedef_pcpo_UU:
fixes Abs :: "'a::pcpo \<Rightarrow> 'b::cpo"
assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
    and UU_in_A: "\<bottom> \<in> A"
shows "OFCLASS('b, pcpo_class)"
by (rule typedef_pcpo [OF type less UU_in_A], rule minimal)


subsubsection {* Strictness of @{term Rep} and @{term Abs} *}

text {*
  For a sub-pcpo where @{term \<bottom>} is a member of the defining
  subset, @{term Rep} and @{term Abs} are both strict.
*}

theorem typedef_strict_Abs:
assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
    and UU_in_A: "\<bottom> \<in> A"
shows "Abs \<bottom> = \<bottom>"
 apply (rule UU_I, unfold less)
 apply (simp add: type_definition.Abs_inverse [OF type UU_in_A])
done

theorem typedef_strict_Rep:
assumes type: "type_definition Rep Abs A"
    and less: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
    and UU_in_A: "\<bottom> \<in> A"
shows "Rep \<bottom> = \<bottom>"
 apply (rule typedef_strict_Abs [OF type less UU_in_A, THEN subst])
 apply (rule type_definition.Abs_inverse [OF type UU_in_A])
done

end
