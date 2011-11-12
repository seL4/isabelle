(*  Title:      HOL/UNITY/Guar.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Sidi Ehmety

From Chandy and Sanders, "Reasoning About Program Composition",
Technical Report 2000-003, University of Florida, 2000.

Compatibility, weakest guarantees, etc.  and Weakest existential
property, from Charpentier and Chandy "Theorems about Composition",
Fifth International Conference on Mathematics of Program, 2000.
*)

header{*Guarantees Specifications*}

theory Guar
imports Comp
begin

instance program :: (type) order
proof qed (auto simp add: program_less_le dest: component_antisym intro: component_refl component_trans)

text{*Existential and Universal properties.  I formalize the two-program
      case, proving equivalence with Chandy and Sanders's n-ary definitions*}

definition ex_prop :: "'a program set => bool" where
   "ex_prop X == \<forall>F G. F ok G -->F \<in> X | G \<in> X --> (F\<squnion>G) \<in> X"

definition strict_ex_prop  :: "'a program set => bool" where
   "strict_ex_prop X == \<forall>F G.  F ok G --> (F \<in> X | G \<in> X) = (F\<squnion>G \<in> X)"

definition uv_prop  :: "'a program set => bool" where
   "uv_prop X == SKIP \<in> X & (\<forall>F G. F ok G --> F \<in> X & G \<in> X --> (F\<squnion>G) \<in> X)"

definition strict_uv_prop  :: "'a program set => bool" where
   "strict_uv_prop X == 
      SKIP \<in> X & (\<forall>F G. F ok G --> (F \<in> X & G \<in> X) = (F\<squnion>G \<in> X))"


text{*Guarantees properties*}

definition guar :: "['a program set, 'a program set] => 'a program set" (infixl "guarantees" 55) where
          (*higher than membership, lower than Co*)
   "X guarantees Y == {F. \<forall>G. F ok G --> F\<squnion>G \<in> X --> F\<squnion>G \<in> Y}"
  

  (* Weakest guarantees *)
definition wg :: "['a program, 'a program set] => 'a program set" where
  "wg F Y == Union({X. F \<in> X guarantees Y})"

   (* Weakest existential property stronger than X *)
definition wx :: "('a program) set => ('a program)set" where
   "wx X == Union({Y. Y \<subseteq> X & ex_prop Y})"
  
  (*Ill-defined programs can arise through "Join"*)
definition welldef :: "'a program set" where
  "welldef == {F. Init F \<noteq> {}}"
  
definition refines :: "['a program, 'a program, 'a program set] => bool"
                        ("(3_ refines _ wrt _)" [10,10,10] 10) where
  "G refines F wrt X ==
     \<forall>H. (F ok H & G ok H & F\<squnion>H \<in> welldef \<inter> X) --> 
         (G\<squnion>H \<in> welldef \<inter> X)"

definition iso_refines :: "['a program, 'a program, 'a program set] => bool"
                              ("(3_ iso'_refines _ wrt _)" [10,10,10] 10) where
  "G iso_refines F wrt X ==
   F \<in> welldef \<inter> X --> G \<in> welldef \<inter> X"


lemma OK_insert_iff:
     "(OK (insert i I) F) = 
      (if i \<in> I then OK I F else OK I F & (F i ok JOIN I F))"
by (auto intro: ok_sym simp add: OK_iff_ok)


subsection{*Existential Properties*}

lemma ex1:
  assumes "ex_prop X" and "finite GG"
  shows "GG \<inter> X \<noteq> {} \<Longrightarrow> OK GG (%G. G) \<Longrightarrow> (\<Squnion>G \<in> GG. G) \<in> X"
  apply (atomize (full))
  using assms(2) apply induct
   using assms(1) apply (unfold ex_prop_def)
   apply (auto simp add: OK_insert_iff Int_insert_left)
  done

lemma ex2: 
     "\<forall>GG. finite GG & GG \<inter> X \<noteq> {} --> OK GG (%G. G) -->(\<Squnion>G \<in> GG. G):X 
      ==> ex_prop X"
apply (unfold ex_prop_def, clarify)
apply (drule_tac x = "{F,G}" in spec)
apply (auto dest: ok_sym simp add: OK_iff_ok)
done


(*Chandy & Sanders take this as a definition*)
lemma ex_prop_finite:
     "ex_prop X = 
      (\<forall>GG. finite GG & GG \<inter> X \<noteq> {} & OK GG (%G. G)--> (\<Squnion>G \<in> GG. G) \<in> X)"
by (blast intro: ex1 ex2)


(*Their "equivalent definition" given at the end of section 3*)
lemma ex_prop_equiv: 
     "ex_prop X = (\<forall>G. G \<in> X = (\<forall>H. (G component_of H) --> H \<in> X))"
apply auto
apply (unfold ex_prop_def component_of_def, safe, blast, blast) 
apply (subst Join_commute) 
apply (drule ok_sym, blast) 
done


subsection{*Universal Properties*}

lemma uv1:
  assumes "uv_prop X"
    and "finite GG"
    and "GG \<subseteq> X"
    and "OK GG (%G. G)"
  shows "(\<Squnion>G \<in> GG. G) \<in> X"
  using assms(2-)
  apply induct
   using assms(1)
   apply (unfold uv_prop_def)
   apply (auto simp add: Int_insert_left OK_insert_iff)
  done

lemma uv2: 
     "\<forall>GG. finite GG & GG \<subseteq> X & OK GG (%G. G) --> (\<Squnion>G \<in> GG. G) \<in> X  
      ==> uv_prop X"
apply (unfold uv_prop_def)
apply (rule conjI)
 apply (drule_tac x = "{}" in spec)
 prefer 2
 apply clarify 
 apply (drule_tac x = "{F,G}" in spec)
apply (auto dest: ok_sym simp add: OK_iff_ok)
done

(*Chandy & Sanders take this as a definition*)
lemma uv_prop_finite:
     "uv_prop X = 
      (\<forall>GG. finite GG & GG \<subseteq> X & OK GG (%G. G) --> (\<Squnion>G \<in> GG. G): X)"
by (blast intro: uv1 uv2)

subsection{*Guarantees*}

lemma guaranteesI:
     "(!!G. [| F ok G; F\<squnion>G \<in> X |] ==> F\<squnion>G \<in> Y) ==> F \<in> X guarantees Y"
by (simp add: guar_def component_def)

lemma guaranteesD: 
     "[| F \<in> X guarantees Y;  F ok G;  F\<squnion>G \<in> X |] ==> F\<squnion>G \<in> Y"
by (unfold guar_def component_def, blast)

(*This version of guaranteesD matches more easily in the conclusion
  The major premise can no longer be  F \<subseteq> H since we need to reason about G*)
lemma component_guaranteesD: 
     "[| F \<in> X guarantees Y;  F\<squnion>G = H;  H \<in> X;  F ok G |] ==> H \<in> Y"
by (unfold guar_def, blast)

lemma guarantees_weaken: 
     "[| F \<in> X guarantees X'; Y \<subseteq> X; X' \<subseteq> Y' |] ==> F \<in> Y guarantees Y'"
by (unfold guar_def, blast)

lemma subset_imp_guarantees_UNIV: "X \<subseteq> Y ==> X guarantees Y = UNIV"
by (unfold guar_def, blast)

(*Equivalent to subset_imp_guarantees_UNIV but more intuitive*)
lemma subset_imp_guarantees: "X \<subseteq> Y ==> F \<in> X guarantees Y"
by (unfold guar_def, blast)

(*Remark at end of section 4.1 *)

lemma ex_prop_imp: "ex_prop Y ==> (Y = UNIV guarantees Y)"
apply (simp (no_asm_use) add: guar_def ex_prop_equiv)
apply safe
 apply (drule_tac x = x in spec)
 apply (drule_tac [2] x = x in spec)
 apply (drule_tac [2] sym)
apply (auto simp add: component_of_def)
done

lemma guarantees_imp: "(Y = UNIV guarantees Y) ==> ex_prop(Y)"
by (auto simp add: guar_def ex_prop_equiv component_of_def dest: sym)

lemma ex_prop_equiv2: "(ex_prop Y) = (Y = UNIV guarantees Y)"
apply (rule iffI)
apply (rule ex_prop_imp)
apply (auto simp add: guarantees_imp) 
done


subsection{*Distributive Laws.  Re-Orient to Perform Miniscoping*}

lemma guarantees_UN_left: 
     "(\<Union>i \<in> I. X i) guarantees Y = (\<Inter>i \<in> I. X i guarantees Y)"
by (unfold guar_def, blast)

lemma guarantees_Un_left: 
     "(X \<union> Y) guarantees Z = (X guarantees Z) \<inter> (Y guarantees Z)"
by (unfold guar_def, blast)

lemma guarantees_INT_right: 
     "X guarantees (\<Inter>i \<in> I. Y i) = (\<Inter>i \<in> I. X guarantees Y i)"
by (unfold guar_def, blast)

lemma guarantees_Int_right: 
     "Z guarantees (X \<inter> Y) = (Z guarantees X) \<inter> (Z guarantees Y)"
by (unfold guar_def, blast)

lemma guarantees_Int_right_I:
     "[| F \<in> Z guarantees X;  F \<in> Z guarantees Y |]  
     ==> F \<in> Z guarantees (X \<inter> Y)"
by (simp add: guarantees_Int_right)

lemma guarantees_INT_right_iff:
     "(F \<in> X guarantees (INTER I Y)) = (\<forall>i\<in>I. F \<in> X guarantees (Y i))"
by (simp add: guarantees_INT_right)

lemma shunting: "(X guarantees Y) = (UNIV guarantees (-X \<union> Y))"
by (unfold guar_def, blast)

lemma contrapositive: "(X guarantees Y) = -Y guarantees -X"
by (unfold guar_def, blast)

(** The following two can be expressed using intersection and subset, which
    is more faithful to the text but looks cryptic.
**)

lemma combining1: 
    "[| F \<in> V guarantees X;  F \<in> (X \<inter> Y) guarantees Z |] 
     ==> F \<in> (V \<inter> Y) guarantees Z"
by (unfold guar_def, blast)

lemma combining2: 
    "[| F \<in> V guarantees (X \<union> Y);  F \<in> Y guarantees Z |] 
     ==> F \<in> V guarantees (X \<union> Z)"
by (unfold guar_def, blast)

(** The following two follow Chandy-Sanders, but the use of object-quantifiers
    does not suit Isabelle... **)

(*Premise should be (!!i. i \<in> I ==> F \<in> X guarantees Y i) *)
lemma all_guarantees: 
     "\<forall>i\<in>I. F \<in> X guarantees (Y i) ==> F \<in> X guarantees (\<Inter>i \<in> I. Y i)"
by (unfold guar_def, blast)

(*Premises should be [| F \<in> X guarantees Y i; i \<in> I |] *)
lemma ex_guarantees: 
     "\<exists>i\<in>I. F \<in> X guarantees (Y i) ==> F \<in> X guarantees (\<Union>i \<in> I. Y i)"
by (unfold guar_def, blast)


subsection{*Guarantees: Additional Laws (by lcp)*}

lemma guarantees_Join_Int: 
    "[| F \<in> U guarantees V;  G \<in> X guarantees Y; F ok G |]  
     ==> F\<squnion>G \<in> (U \<inter> X) guarantees (V \<inter> Y)"
apply (simp add: guar_def, safe)
 apply (simp add: Join_assoc)
apply (subgoal_tac "F\<squnion>G\<squnion>Ga = G\<squnion>(F\<squnion>Ga) ")
 apply (simp add: ok_commute)
apply (simp add: Join_ac)
done

lemma guarantees_Join_Un: 
    "[| F \<in> U guarantees V;  G \<in> X guarantees Y; F ok G |]   
     ==> F\<squnion>G \<in> (U \<union> X) guarantees (V \<union> Y)"
apply (simp add: guar_def, safe)
 apply (simp add: Join_assoc)
apply (subgoal_tac "F\<squnion>G\<squnion>Ga = G\<squnion>(F\<squnion>Ga) ")
 apply (simp add: ok_commute)
apply (simp add: Join_ac)
done

lemma guarantees_JN_INT: 
     "[| \<forall>i\<in>I. F i \<in> X i guarantees Y i;  OK I F |]  
      ==> (JOIN I F) \<in> (INTER I X) guarantees (INTER I Y)"
apply (unfold guar_def, auto)
apply (drule bspec, assumption)
apply (rename_tac "i")
apply (drule_tac x = "JOIN (I-{i}) F\<squnion>G" in spec)
apply (auto intro: OK_imp_ok
            simp add: Join_assoc [symmetric] JN_Join_diff JN_absorb)
done

lemma guarantees_JN_UN: 
    "[| \<forall>i\<in>I. F i \<in> X i guarantees Y i;  OK I F |]  
     ==> (JOIN I F) \<in> (UNION I X) guarantees (UNION I Y)"
apply (unfold guar_def, auto)
apply (drule bspec, assumption)
apply (rename_tac "i")
apply (drule_tac x = "JOIN (I-{i}) F\<squnion>G" in spec)
apply (auto intro: OK_imp_ok
            simp add: Join_assoc [symmetric] JN_Join_diff JN_absorb)
done


subsection{*Guarantees Laws for Breaking Down the Program (by lcp)*}

lemma guarantees_Join_I1: 
     "[| F \<in> X guarantees Y;  F ok G |] ==> F\<squnion>G \<in> X guarantees Y"
by (simp add: guar_def Join_assoc)

lemma guarantees_Join_I2:         
     "[| G \<in> X guarantees Y;  F ok G |] ==> F\<squnion>G \<in> X guarantees Y"
apply (simp add: Join_commute [of _ G] ok_commute [of _ G])
apply (blast intro: guarantees_Join_I1)
done

lemma guarantees_JN_I: 
     "[| i \<in> I;  F i \<in> X guarantees Y;  OK I F |]  
      ==> (\<Squnion>i \<in> I. (F i)) \<in> X guarantees Y"
apply (unfold guar_def, clarify)
apply (drule_tac x = "JOIN (I-{i}) F\<squnion>G" in spec)
apply (auto intro: OK_imp_ok simp add: JN_Join_diff Join_assoc [symmetric])
done


(*** well-definedness ***)

lemma Join_welldef_D1: "F\<squnion>G \<in> welldef ==> F \<in> welldef"
by (unfold welldef_def, auto)

lemma Join_welldef_D2: "F\<squnion>G \<in> welldef ==> G \<in> welldef"
by (unfold welldef_def, auto)

(*** refinement ***)

lemma refines_refl: "F refines F wrt X"
by (unfold refines_def, blast)

(*We'd like transitivity, but how do we get it?*)
lemma refines_trans:
     "[| H refines G wrt X;  G refines F wrt X |] ==> H refines F wrt X"
apply (simp add: refines_def) 
oops


lemma strict_ex_refine_lemma: 
     "strict_ex_prop X  
      ==> (\<forall>H. F ok H & G ok H & F\<squnion>H \<in> X --> G\<squnion>H \<in> X)  
              = (F \<in> X --> G \<in> X)"
by (unfold strict_ex_prop_def, auto)

lemma strict_ex_refine_lemma_v: 
     "strict_ex_prop X  
      ==> (\<forall>H. F ok H & G ok H & F\<squnion>H \<in> welldef & F\<squnion>H \<in> X --> G\<squnion>H \<in> X) =  
          (F \<in> welldef \<inter> X --> G \<in> X)"
apply (unfold strict_ex_prop_def, safe)
apply (erule_tac x = SKIP and P = "%H. ?PP H --> ?RR H" in allE)
apply (auto dest: Join_welldef_D1 Join_welldef_D2)
done

lemma ex_refinement_thm:
     "[| strict_ex_prop X;   
         \<forall>H. F ok H & G ok H & F\<squnion>H \<in> welldef \<inter> X --> G\<squnion>H \<in> welldef |]  
      ==> (G refines F wrt X) = (G iso_refines F wrt X)"
apply (rule_tac x = SKIP in allE, assumption)
apply (simp add: refines_def iso_refines_def strict_ex_refine_lemma_v)
done


lemma strict_uv_refine_lemma: 
     "strict_uv_prop X ==> 
      (\<forall>H. F ok H & G ok H & F\<squnion>H \<in> X --> G\<squnion>H \<in> X) = (F \<in> X --> G \<in> X)"
by (unfold strict_uv_prop_def, blast)

lemma strict_uv_refine_lemma_v: 
     "strict_uv_prop X  
      ==> (\<forall>H. F ok H & G ok H & F\<squnion>H \<in> welldef & F\<squnion>H \<in> X --> G\<squnion>H \<in> X) =  
          (F \<in> welldef \<inter> X --> G \<in> X)"
apply (unfold strict_uv_prop_def, safe)
apply (erule_tac x = SKIP and P = "%H. ?PP H --> ?RR H" in allE)
apply (auto dest: Join_welldef_D1 Join_welldef_D2)
done

lemma uv_refinement_thm:
     "[| strict_uv_prop X;   
         \<forall>H. F ok H & G ok H & F\<squnion>H \<in> welldef \<inter> X --> 
             G\<squnion>H \<in> welldef |]  
      ==> (G refines F wrt X) = (G iso_refines F wrt X)"
apply (rule_tac x = SKIP in allE, assumption)
apply (simp add: refines_def iso_refines_def strict_uv_refine_lemma_v)
done

(* Added by Sidi Ehmety from Chandy & Sander, section 6 *)
lemma guarantees_equiv: 
    "(F \<in> X guarantees Y) = (\<forall>H. H \<in> X \<longrightarrow> (F component_of H \<longrightarrow> H \<in> Y))"
by (unfold guar_def component_of_def, auto)

lemma wg_weakest: "!!X. F\<in> (X guarantees Y) ==> X \<subseteq> (wg F Y)"
by (unfold wg_def, auto)

lemma wg_guarantees: "F\<in> ((wg F Y) guarantees Y)"
by (unfold wg_def guar_def, blast)

lemma wg_equiv: "(H \<in> wg F X) = (F component_of H --> H \<in> X)"
by (simp add: guarantees_equiv wg_def, blast)

lemma component_of_wg: "F component_of H ==> (H \<in> wg F X) = (H \<in> X)"
by (simp add: wg_equiv)

lemma wg_finite: 
    "\<forall>FF. finite FF & FF \<inter> X \<noteq> {} --> OK FF (%F. F)  
          --> (\<forall>F\<in>FF. ((\<Squnion>F \<in> FF. F): wg F X) = ((\<Squnion>F \<in> FF. F):X))"
apply clarify
apply (subgoal_tac "F component_of (\<Squnion>F \<in> FF. F) ")
apply (drule_tac X = X in component_of_wg, simp)
apply (simp add: component_of_def)
apply (rule_tac x = "\<Squnion>F \<in> (FF-{F}) . F" in exI)
apply (auto intro: JN_Join_diff dest: ok_sym simp add: OK_iff_ok)
done

lemma wg_ex_prop: "ex_prop X ==> (F \<in> X) = (\<forall>H. H \<in> wg F X)"
apply (simp (no_asm_use) add: ex_prop_equiv wg_equiv)
apply blast
done

(** From Charpentier and Chandy "Theorems About Composition" **)
(* Proposition 2 *)
lemma wx_subset: "(wx X)<=X"
by (unfold wx_def, auto)

lemma wx_ex_prop: "ex_prop (wx X)"
apply (simp add: wx_def ex_prop_equiv cong: bex_cong, safe, blast)
apply force 
done

lemma wx_weakest: "\<forall>Z. Z<= X --> ex_prop Z --> Z \<subseteq> wx X"
by (auto simp add: wx_def)

(* Proposition 6 *)
lemma wx'_ex_prop: "ex_prop({F. \<forall>G. F ok G --> F\<squnion>G \<in> X})"
apply (unfold ex_prop_def, safe)
 apply (drule_tac x = "G\<squnion>Ga" in spec)
 apply (force simp add: Join_assoc)
apply (drule_tac x = "F\<squnion>Ga" in spec)
apply (simp add: ok_commute  Join_ac) 
done

text{* Equivalence with the other definition of wx *}

lemma wx_equiv: "wx X = {F. \<forall>G. F ok G --> (F\<squnion>G) \<in> X}"
apply (unfold wx_def, safe)
 apply (simp add: ex_prop_def, blast) 
apply (simp (no_asm))
apply (rule_tac x = "{F. \<forall>G. F ok G --> F\<squnion>G \<in> X}" in exI, safe)
apply (rule_tac [2] wx'_ex_prop)
apply (drule_tac x = SKIP in spec)+
apply auto 
done


text{* Propositions 7 to 11 are about this second definition of wx. 
   They are the same as the ones proved for the first definition of wx,
 by equivalence *}
   
(* Proposition 12 *)
(* Main result of the paper *)
lemma guarantees_wx_eq: "(X guarantees Y) = wx(-X \<union> Y)"
by (simp add: guar_def wx_equiv)


(* Rules given in section 7 of Chandy and Sander's
    Reasoning About Program composition paper *)
lemma stable_guarantees_Always:
     "Init F \<subseteq> A ==> F \<in> (stable A) guarantees (Always A)"
apply (rule guaranteesI)
apply (simp add: Join_commute)
apply (rule stable_Join_Always1)
 apply (simp_all add: invariant_def)
done

lemma constrains_guarantees_leadsTo:
     "F \<in> transient A ==> F \<in> (A co A \<union> B) guarantees (A leadsTo (B-A))"
apply (rule guaranteesI)
apply (rule leadsTo_Basis')
 apply (drule constrains_weaken_R)
  prefer 2 apply assumption
 apply blast
apply (blast intro: Join_transient_I1)
done

end
