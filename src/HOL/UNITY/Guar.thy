(*  Title:      HOL/UNITY/Guar.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Guarantees, etc.

From Chandy and Sanders, "Reasoning About Program Composition",
Technical Report 2000-003, University of Florida, 2000.

Revised by Sidi Ehmety on January 2001

Added: Compatibility, weakest guarantees, etc.

and Weakest existential property,
from Charpentier and Chandy "Theorems about Composition",
Fifth International Conference on Mathematics of Program, 2000.

*)

theory Guar = Comp:

instance program :: (type) order
  by (intro_classes,
      (assumption | rule component_refl component_trans component_antisym
                     program_less_le)+)


constdefs

  (*Existential and Universal properties.  I formalize the two-program
    case, proving equivalence with Chandy and Sanders's n-ary definitions*)

  ex_prop  :: "'a program set => bool"
   "ex_prop X == \<forall>F G. F ok G -->F:X | G: X --> (F Join G) : X"

  strict_ex_prop  :: "'a program set => bool"
   "strict_ex_prop X == \<forall>F G.  F ok G --> (F:X | G: X) = (F Join G : X)"

  uv_prop  :: "'a program set => bool"
   "uv_prop X == SKIP : X & (\<forall>F G. F ok G --> F:X & G: X --> (F Join G) : X)"

  strict_uv_prop  :: "'a program set => bool"
   "strict_uv_prop X == 
      SKIP : X & (\<forall>F G. F ok G --> (F:X & G: X) = (F Join G : X))"

  guar :: "['a program set, 'a program set] => 'a program set"
          (infixl "guarantees" 55)  (*higher than membership, lower than Co*)
   "X guarantees Y == {F. \<forall>G. F ok G --> F Join G : X --> F Join G : Y}"
  

  (* Weakest guarantees *)
   wg :: "['a program, 'a program set] =>  'a program set"
  "wg F Y == Union({X. F:X guarantees Y})"

   (* Weakest existential property stronger than X *)
   wx :: "('a program) set => ('a program)set"
   "wx X == Union({Y. Y<=X & ex_prop Y})"
  
  (*Ill-defined programs can arise through "Join"*)
  welldef :: "'a program set"
  "welldef == {F. Init F ~= {}}"
  
  refines :: "['a program, 'a program, 'a program set] => bool"
			("(3_ refines _ wrt _)" [10,10,10] 10)
  "G refines F wrt X ==
     \<forall>H. (F ok H  & G ok H & F Join H : welldef Int X) --> 
         (G Join H : welldef Int X)"

  iso_refines :: "['a program, 'a program, 'a program set] => bool"
                              ("(3_ iso'_refines _ wrt _)" [10,10,10] 10)
  "G iso_refines F wrt X ==
   F : welldef Int X --> G : welldef Int X"


lemma OK_insert_iff:
     "(OK (insert i I) F) = 
      (if i:I then OK I F else OK I F & (F i ok JOIN I F))"
by (auto intro: ok_sym simp add: OK_iff_ok)


(*** existential properties ***)
lemma ex1 [rule_format (no_asm)]: 
 "[| ex_prop X; finite GG |] ==>  
     GG Int X ~= {}--> OK GG (%G. G) -->(JN G:GG. G) : X"
apply (unfold ex_prop_def)
apply (erule finite_induct)
apply (auto simp add: OK_insert_iff Int_insert_left)
done


lemma ex2: 
     "\<forall>GG. finite GG & GG Int X ~= {} --> OK GG (%G. G) -->(JN G:GG. G):X 
      ==> ex_prop X"
apply (unfold ex_prop_def, clarify)
apply (drule_tac x = "{F,G}" in spec)
apply (auto dest: ok_sym simp add: OK_iff_ok)
done


(*Chandy & Sanders take this as a definition*)
lemma ex_prop_finite:
     "ex_prop X = 
      (\<forall>GG. finite GG & GG Int X ~= {} & OK GG (%G. G)--> (JN G:GG. G) : X)"
by (blast intro: ex1 ex2)


(*Their "equivalent definition" given at the end of section 3*)
lemma ex_prop_equiv: 
     "ex_prop X = (\<forall>G. G:X = (\<forall>H. (G component_of H) --> H: X))"
apply auto
apply (unfold ex_prop_def component_of_def, safe)
apply blast 
apply blast 
apply (subst Join_commute) 
apply (drule ok_sym, blast) 
done


(*** universal properties ***)
lemma uv1 [rule_format]: 
     "[| uv_prop X; finite GG |] 
      ==> GG <= X & OK GG (%G. G) --> (JN G:GG. G) : X"
apply (unfold uv_prop_def)
apply (erule finite_induct)
apply (auto simp add: Int_insert_left OK_insert_iff)
done

lemma uv2: 
     "\<forall>GG. finite GG & GG <= X & OK GG (%G. G) --> (JN G:GG. G) : X  
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
      (\<forall>GG. finite GG & GG <= X & OK GG (%G. G) --> (JN G:GG. G): X)"
by (blast intro: uv1 uv2)

(*** guarantees ***)

lemma guaranteesI:
     "(!!G. [| F ok G; F Join G : X |] ==> F Join G : Y)  
      ==> F : X guarantees Y"
by (simp add: guar_def component_def)

lemma guaranteesD: 
     "[| F : X guarantees Y;  F ok G;  F Join G : X |]  
      ==> F Join G : Y"
by (unfold guar_def component_def, blast)

(*This version of guaranteesD matches more easily in the conclusion
  The major premise can no longer be  F<=H since we need to reason about G*)
lemma component_guaranteesD: 
     "[| F : X guarantees Y;  F Join G = H;  H : X;  F ok G |]  
      ==> H : Y"
by (unfold guar_def, blast)

lemma guarantees_weaken: 
     "[| F: X guarantees X'; Y <= X; X' <= Y' |] ==> F: Y guarantees Y'"
by (unfold guar_def, blast)

lemma subset_imp_guarantees_UNIV: "X <= Y ==> X guarantees Y = UNIV"
by (unfold guar_def, blast)

(*Equivalent to subset_imp_guarantees_UNIV but more intuitive*)
lemma subset_imp_guarantees: "X <= Y ==> F : X guarantees Y"
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
apply (simp (no_asm_use) add: guar_def ex_prop_equiv)
apply safe
apply (auto simp add: component_of_def dest: sym)
done

lemma ex_prop_equiv2: "(ex_prop Y) = (Y = UNIV guarantees Y)"
apply (rule iffI)
apply (rule ex_prop_imp)
apply (auto simp add: guarantees_imp) 
done


(** Distributive laws.  Re-orient to perform miniscoping **)

lemma guarantees_UN_left: 
     "(UN i:I. X i) guarantees Y = (INT i:I. X i guarantees Y)"
by (unfold guar_def, blast)

lemma guarantees_Un_left: 
     "(X Un Y) guarantees Z = (X guarantees Z) Int (Y guarantees Z)"
by (unfold guar_def, blast)

lemma guarantees_INT_right: 
     "X guarantees (INT i:I. Y i) = (INT i:I. X guarantees Y i)"
by (unfold guar_def, blast)

lemma guarantees_Int_right: 
     "Z guarantees (X Int Y) = (Z guarantees X) Int (Z guarantees Y)"
by (unfold guar_def, blast)

lemma guarantees_Int_right_I:
     "[| F : Z guarantees X;  F : Z guarantees Y |]  
     ==> F : Z guarantees (X Int Y)"
by (simp add: guarantees_Int_right)

lemma guarantees_INT_right_iff:
     "(F : X guarantees (INTER I Y)) = (\<forall>i\<in>I. F : X guarantees (Y i))"
by (simp add: guarantees_INT_right)

lemma shunting: "(X guarantees Y) = (UNIV guarantees (-X Un Y))"
by (unfold guar_def, blast)

lemma contrapositive: "(X guarantees Y) = -Y guarantees -X"
by (unfold guar_def, blast)

(** The following two can be expressed using intersection and subset, which
    is more faithful to the text but looks cryptic.
**)

lemma combining1: 
    "[| F : V guarantees X;  F : (X Int Y) guarantees Z |] 
     ==> F : (V Int Y) guarantees Z"

by (unfold guar_def, blast)

lemma combining2: 
    "[| F : V guarantees (X Un Y);  F : Y guarantees Z |] 
     ==> F : V guarantees (X Un Z)"
by (unfold guar_def, blast)

(** The following two follow Chandy-Sanders, but the use of object-quantifiers
    does not suit Isabelle... **)

(*Premise should be (!!i. i: I ==> F: X guarantees Y i) *)
lemma all_guarantees: 
     "\<forall>i\<in>I. F : X guarantees (Y i) ==> F : X guarantees (INT i:I. Y i)"
by (unfold guar_def, blast)

(*Premises should be [| F: X guarantees Y i; i: I |] *)
lemma ex_guarantees: 
     "\<exists>i\<in>I. F : X guarantees (Y i) ==> F : X guarantees (UN i:I. Y i)"
by (unfold guar_def, blast)


(*** Additional guarantees laws, by lcp ***)

lemma guarantees_Join_Int: 
    "[| F: U guarantees V;  G: X guarantees Y; F ok G |]  
     ==> F Join G: (U Int X) guarantees (V Int Y)"
apply (unfold guar_def)
apply (simp (no_asm))
apply safe
apply (simp add: Join_assoc)
apply (subgoal_tac "F Join G Join Ga = G Join (F Join Ga) ")
apply (simp add: ok_commute)
apply (simp (no_asm_simp) add: Join_ac)
done

lemma guarantees_Join_Un: 
    "[| F: U guarantees V;  G: X guarantees Y; F ok G |]   
     ==> F Join G: (U Un X) guarantees (V Un Y)"
apply (unfold guar_def)
apply (simp (no_asm))
apply safe
apply (simp add: Join_assoc)
apply (subgoal_tac "F Join G Join Ga = G Join (F Join Ga) ")
apply (simp add: ok_commute)
apply (simp (no_asm_simp) add: Join_ac)
done

lemma guarantees_JN_INT: 
     "[| \<forall>i\<in>I. F i : X i guarantees Y i;  OK I F |]  
      ==> (JOIN I F) : (INTER I X) guarantees (INTER I Y)"
apply (unfold guar_def, auto)
apply (drule bspec, assumption)
apply (rename_tac "i")
apply (drule_tac x = "JOIN (I-{i}) F Join G" in spec)
apply (auto intro: OK_imp_ok
            simp add: Join_assoc [symmetric] JN_Join_diff JN_absorb)
done

lemma guarantees_JN_UN: 
    "[| \<forall>i\<in>I. F i : X i guarantees Y i;  OK I F |]  
     ==> (JOIN I F) : (UNION I X) guarantees (UNION I Y)"
apply (unfold guar_def, auto)
apply (drule bspec, assumption)
apply (rename_tac "i")
apply (drule_tac x = "JOIN (I-{i}) F Join G" in spec)
apply (auto intro: OK_imp_ok
            simp add: Join_assoc [symmetric] JN_Join_diff JN_absorb)
done


(*** guarantees laws for breaking down the program, by lcp ***)

lemma guarantees_Join_I1: 
     "[| F: X guarantees Y;  F ok G |] ==> F Join G: X guarantees Y"
apply (unfold guar_def)
apply (simp (no_asm))
apply safe
apply (simp add: Join_assoc)
done

lemma guarantees_Join_I2:
     "[| G: X guarantees Y;  F ok G |] ==> F Join G: X guarantees Y"
apply (simp add: Join_commute [of _ G] ok_commute [of _ G])
apply (blast intro: guarantees_Join_I1)
done

lemma guarantees_JN_I: 
     "[| i : I;  F i: X guarantees Y;  OK I F |]  
      ==> (JN i:I. (F i)) : X guarantees Y"
apply (unfold guar_def, clarify)
apply (drule_tac x = "JOIN (I-{i}) F Join G" in spec)
apply (auto intro: OK_imp_ok simp add: JN_Join_diff JN_Join_diff Join_assoc [symmetric])
done


(*** well-definedness ***)

lemma Join_welldef_D1: "F Join G: welldef ==> F: welldef"
by (unfold welldef_def, auto)

lemma Join_welldef_D2: "F Join G: welldef ==> G: welldef"
by (unfold welldef_def, auto)

(*** refinement ***)

lemma refines_refl: "F refines F wrt X"
by (unfold refines_def, blast)


(* Goalw [refines_def]
     "[| H refines G wrt X;  G refines F wrt X |] ==> H refines F wrt X"
by Auto_tac
qed "refines_trans"; *)



lemma strict_ex_refine_lemma: 
     "strict_ex_prop X  
      ==> (\<forall>H. F ok H & G ok H & F Join H : X --> G Join H : X)  
              = (F:X --> G:X)"
by (unfold strict_ex_prop_def, auto)

lemma strict_ex_refine_lemma_v: 
     "strict_ex_prop X  
      ==> (\<forall>H. F ok H & G ok H & F Join H : welldef & F Join H : X --> G Join H : X) =  
          (F: welldef Int X --> G:X)"
apply (unfold strict_ex_prop_def, safe)
apply (erule_tac x = SKIP and P = "%H. ?PP H --> ?RR H" in allE)
apply (auto dest: Join_welldef_D1 Join_welldef_D2)
done

lemma ex_refinement_thm:
     "[| strict_ex_prop X;   
         \<forall>H. F ok H & G ok H & F Join H : welldef Int X --> G Join H : welldef |]  
      ==> (G refines F wrt X) = (G iso_refines F wrt X)"
apply (rule_tac x = SKIP in allE, assumption)
apply (simp add: refines_def iso_refines_def strict_ex_refine_lemma_v)
done


lemma strict_uv_refine_lemma: 
     "strict_uv_prop X ==> 
      (\<forall>H. F ok H & G ok H & F Join H : X --> G Join H : X) = (F:X --> G:X)"
by (unfold strict_uv_prop_def, blast)

lemma strict_uv_refine_lemma_v: 
     "strict_uv_prop X  
      ==> (\<forall>H. F ok H & G ok H & F Join H : welldef & F Join H : X --> G Join H : X) =  
          (F: welldef Int X --> G:X)"
apply (unfold strict_uv_prop_def, safe)
apply (erule_tac x = SKIP and P = "%H. ?PP H --> ?RR H" in allE)
apply (auto dest: Join_welldef_D1 Join_welldef_D2)
done

lemma uv_refinement_thm:
     "[| strict_uv_prop X;   
         \<forall>H. F ok H & G ok H & F Join H : welldef Int X --> 
             G Join H : welldef |]  
      ==> (G refines F wrt X) = (G iso_refines F wrt X)"
apply (rule_tac x = SKIP in allE, assumption)
apply (simp add: refines_def iso_refines_def strict_uv_refine_lemma_v)
done

(* Added by Sidi Ehmety from Chandy & Sander, section 6 *)
lemma guarantees_equiv: 
    "(F:X guarantees Y) = (\<forall>H. H:X \<longrightarrow> (F component_of H \<longrightarrow> H:Y))"
by (unfold guar_def component_of_def, auto)

lemma wg_weakest: "!!X. F:(X guarantees Y) ==> X <= (wg F Y)"
by (unfold wg_def, auto)

lemma wg_guarantees: "F:((wg F Y) guarantees Y)"
by (unfold wg_def guar_def, blast)

lemma wg_equiv: 
  "(H: wg F X) = (F component_of H --> H:X)"
apply (unfold wg_def)
apply (simp (no_asm) add: guarantees_equiv)
apply (rule iffI)
apply (rule_tac [2] x = "{H}" in exI)
apply (blast+)
done


lemma component_of_wg: "F component_of H ==> (H:wg F X) = (H:X)"
by (simp add: wg_equiv)

lemma wg_finite: 
    "\<forall>FF. finite FF & FF Int X ~= {} --> OK FF (%F. F)  
          --> (\<forall>F\<in>FF. ((JN F:FF. F): wg F X) = ((JN F:FF. F):X))"
apply clarify
apply (subgoal_tac "F component_of (JN F:FF. F) ")
apply (drule_tac X = X in component_of_wg, simp)
apply (simp add: component_of_def)
apply (rule_tac x = "JN F: (FF-{F}) . F" in exI)
apply (auto intro: JN_Join_diff dest: ok_sym simp add: OK_iff_ok)
done

lemma wg_ex_prop: "ex_prop X ==> (F:X) = (\<forall>H. H : wg F X)"
apply (simp (no_asm_use) add: ex_prop_equiv wg_equiv)
apply blast
done

(** From Charpentier and Chandy "Theorems About Composition" **)
(* Proposition 2 *)
lemma wx_subset: "(wx X)<=X"
by (unfold wx_def, auto)

lemma wx_ex_prop: "ex_prop (wx X)"
apply (unfold wx_def)
apply (simp (no_asm) add: ex_prop_equiv)
apply safe
apply blast
apply auto
done

lemma wx_weakest: "\<forall>Z. Z<= X --> ex_prop Z --> Z <= wx X"
by (unfold wx_def, auto)

(* Proposition 6 *)
lemma wx'_ex_prop: "ex_prop({F. \<forall>G. F ok G --> F Join G:X})"
apply (unfold ex_prop_def, safe)
apply (drule_tac x = "G Join Ga" in spec)
apply (force simp add: ok_Join_iff1 Join_assoc)
apply (drule_tac x = "F Join Ga" in spec)
apply (simp (no_asm_use) add: ok_Join_iff1)
apply safe
apply (simp (no_asm_simp) add: ok_commute)
apply (subgoal_tac "F Join G = G Join F")
apply (simp (no_asm_simp) add: Join_assoc)
apply (simp (no_asm) add: Join_commute)
done

(* Equivalence with the other definition of wx *)

lemma wx_equiv: 
 "wx X = {F. \<forall>G. F ok G --> (F Join G):X}"

apply (unfold wx_def, safe)
apply (simp (no_asm_use) add: ex_prop_def)
apply (drule_tac x = x in spec)
apply (drule_tac x = G in spec)
apply (frule_tac c = "x Join G" in subsetD, safe)
apply (simp (no_asm))
apply (rule_tac x = "{F. \<forall>G. F ok G --> F Join G:X}" in exI, safe)
apply (rule_tac [2] wx'_ex_prop)
apply (rotate_tac 1)
apply (drule_tac x = SKIP in spec, auto)
done


(* Propositions 7 to 11 are about this second definition of wx. And
   they are the same as the ones proved for the first definition of wx by equivalence *)
   
(* Proposition 12 *)
(* Main result of the paper *)
lemma guarantees_wx_eq: 
   "(X guarantees Y) = wx(-X Un Y)"
apply (unfold guar_def)
apply (simp (no_asm) add: wx_equiv)
done

(* {* Corollary, but this result has already been proved elsewhere *}
 "ex_prop(X guarantees Y)"
  by (simp_tac (simpset() addsimps [guar_wx_iff, wx_ex_prop]) 1);
  qed "guarantees_ex_prop";
*)

(* Rules given in section 7 of Chandy and Sander's
    Reasoning About Program composition paper *)

lemma stable_guarantees_Always:
     "Init F <= A ==> F:(stable A) guarantees (Always A)"
apply (rule guaranteesI)
apply (simp (no_asm) add: Join_commute)
apply (rule stable_Join_Always1)
apply (simp_all add: invariant_def Join_stable)
done

(* To be moved to WFair.ML *)
lemma leadsTo_Basis': "[| F:A co A Un B; F:transient A |] ==> F:A leadsTo B"
apply (drule_tac B = "A-B" in constrains_weaken_L)
apply (drule_tac [2] B = "A-B" in transient_strengthen)
apply (rule_tac [3] ensuresI [THEN leadsTo_Basis])
apply (blast+)
done



lemma constrains_guarantees_leadsTo:
     "F : transient A ==> F: (A co A Un B) guarantees (A leadsTo (B-A))"
apply (rule guaranteesI)
apply (rule leadsTo_Basis')
apply (drule constrains_weaken_R)
prefer 2 apply assumption
apply blast
apply (blast intro: Join_transient_I1)
done

end
