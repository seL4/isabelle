(*  Title:      ZF/UNITY/Guar.thy
    ID:         $Id \<in> Guar.thy,v 1.3 2001/11/15 14:51:43 ehmety Exp $
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Guarantees, etc.

From Chandy and Sanders, "Reasoning About Program Composition",
Technical Report 2000-003, University of Florida, 2000.

Revised by Sidi Ehmety on January 2001

Added \<in> Compatibility, weakest guarantees, etc.

and Weakest existential property,
from Charpentier and Chandy "Theorems about Composition",
Fifth International Conference on Mathematics of Program, 2000.

Theory ported from HOL.
*)


header{*The Chandy-Sanders Guarantees Operator*}

theory Guar = Comp: 


(* To be moved to theory WFair???? *)
lemma leadsTo_Basis': "[| F \<in> A co A Un B; F \<in> transient(A); st_set(B) |] ==> F \<in> A leadsTo B"
apply (frule constrainsD2)
apply (drule_tac B = "A-B" in constrains_weaken_L, blast) 
apply (drule_tac B = "A-B" in transient_strengthen, blast) 
apply (blast intro: ensuresI [THEN leadsTo_Basis])
done


constdefs

  (*Existential and Universal properties.  We formalize the two-program
    case, proving equivalence with Chandy and Sanders's n-ary definitions*)

   ex_prop :: "i => o"
   "ex_prop(X) == X<=program &
    (\<forall>F \<in> program. \<forall>G \<in> program. F ok G --> F \<in> X | G \<in> X --> (F Join G) \<in> X)"

  strict_ex_prop  :: "i => o"
  "strict_ex_prop(X) == X<=program &
   (\<forall>F \<in> program. \<forall>G \<in> program. F ok G --> (F \<in> X | G \<in> X) <-> (F Join G \<in> X))"

  uv_prop  :: "i => o"
   "uv_prop(X) == X<=program &
    (SKIP \<in> X & (\<forall>F \<in> program. \<forall>G \<in> program. F ok G --> F \<in> X & G \<in> X --> (F Join G) \<in> X))"
  
 strict_uv_prop  :: "i => o"
   "strict_uv_prop(X) == X<=program &
    (SKIP \<in> X & (\<forall>F \<in> program. \<forall>G \<in> program. F ok G -->(F \<in> X & G \<in> X) <-> (F Join G \<in> X)))"

  guar :: "[i, i] => i" (infixl "guarantees" 55)
              (*higher than membership, lower than Co*)
  "X guarantees Y == {F \<in> program. \<forall>G \<in> program. F ok G --> F Join G \<in> X --> F Join G \<in> Y}"
  
  (* Weakest guarantees *)
   wg :: "[i,i] => i"
  "wg(F,Y) == Union({X \<in> Pow(program). F:(X guarantees Y)})"

  (* Weakest existential property stronger than X *)
   wx :: "i =>i"
   "wx(X) == Union({Y \<in> Pow(program). Y<=X & ex_prop(Y)})"

  (*Ill-defined programs can arise through "Join"*)
  welldef :: i
  "welldef == {F \<in> program. Init(F) \<noteq> 0}"
  
  refines :: "[i, i, i] => o" ("(3_ refines _ wrt _)" [10,10,10] 10)
  "G refines F wrt X ==
   \<forall>H \<in> program. (F ok H  & G ok H & F Join H \<in> welldef Int X)
    --> (G Join H \<in> welldef Int X)"

  iso_refines :: "[i,i, i] => o"  ("(3_ iso'_refines _ wrt _)" [10,10,10] 10)
  "G iso_refines F wrt X ==  F \<in> welldef Int X --> G \<in> welldef Int X"


(*** existential properties ***)

lemma ex_imp_subset_program: "ex_prop(X) ==> X\<subseteq>program"
by (simp add: ex_prop_def)

lemma ex1 [rule_format]: 
 "GG \<in> Fin(program) 
  ==> ex_prop(X) --> GG Int X\<noteq>0 --> OK(GG, (%G. G)) -->(\<Squnion>G \<in> GG. G) \<in> X"
apply (unfold ex_prop_def)
apply (erule Fin_induct)
apply (simp_all add: OK_cons_iff)
apply (safe elim!: not_emptyE, auto) 
done

lemma ex2 [rule_format]: 
"X \<subseteq> program ==>  
 (\<forall>GG \<in> Fin(program). GG Int X \<noteq> 0 --> OK(GG,(%G. G))-->(\<Squnion>G \<in> GG. G) \<in> X) 
   --> ex_prop(X)"
apply (unfold ex_prop_def, clarify)
apply (drule_tac x = "{F,G}" in bspec)
apply (simp_all add: OK_iff_ok)
apply (auto intro: ok_sym)
done

(*Chandy & Sanders take this as a definition*)

lemma ex_prop_finite:
     "ex_prop(X) <-> (X\<subseteq>program &  
  (\<forall>GG \<in> Fin(program). GG Int X \<noteq> 0 & OK(GG,(%G. G))-->(\<Squnion>G \<in> GG. G) \<in> X))"
apply auto
apply (blast intro: ex1 ex2 dest: ex_imp_subset_program)+
done

(* Equivalent definition of ex_prop given at the end of section 3*)
lemma ex_prop_equiv: 
"ex_prop(X) <->  
  X\<subseteq>program & (\<forall>G \<in> program. (G \<in> X <-> (\<forall>H \<in> program. (G component_of H) --> H \<in> X)))"
apply (unfold ex_prop_def component_of_def, safe, force, force, blast) 
apply (subst Join_commute)
apply (blast intro: ok_sym) 
done

(*** universal properties ***)

lemma uv_imp_subset_program: "uv_prop(X)==> X\<subseteq>program"
apply (unfold uv_prop_def)
apply (simp (no_asm_simp))
done

lemma uv1 [rule_format]: 
     "GG \<in> Fin(program) ==>  
      (uv_prop(X)--> GG \<subseteq> X & OK(GG, (%G. G)) --> (\<Squnion>G \<in> GG. G) \<in> X)"
apply (unfold uv_prop_def)
apply (erule Fin_induct)
apply (auto simp add: OK_cons_iff)
done

lemma uv2 [rule_format]: 
     "X\<subseteq>program  ==> 
      (\<forall>GG \<in> Fin(program). GG \<subseteq> X & OK(GG,(%G. G)) --> (\<Squnion>G \<in> GG. G) \<in> X)
      --> uv_prop(X)"
apply (unfold uv_prop_def, auto)
apply (drule_tac x = 0 in bspec, simp+) 
apply (drule_tac x = "{F,G}" in bspec, simp) 
apply (force dest: ok_sym simp add: OK_iff_ok) 
done

(*Chandy & Sanders take this as a definition*)
lemma uv_prop_finite: 
"uv_prop(X) <-> X\<subseteq>program &  
  (\<forall>GG \<in> Fin(program). GG \<subseteq> X & OK(GG, %G. G) --> (\<Squnion>G \<in> GG. G) \<in>  X)"
apply auto
apply (blast dest: uv_imp_subset_program)
apply (blast intro: uv1)
apply (blast intro!: uv2 dest:)
done

(*** guarantees ***)
lemma guaranteesI: 
     "[| (!!G. [| F ok G; F Join G \<in> X; G \<in> program |] ==> F Join G \<in> Y); 
         F \<in> program |]   
    ==> F \<in> X guarantees Y"
by (simp add: guar_def component_def)

lemma guaranteesD: 
     "[| F \<in> X guarantees Y;  F ok G;  F Join G \<in> X; G \<in> program |]  
      ==> F Join G \<in> Y"
by (simp add: guar_def component_def)


(*This version of guaranteesD matches more easily in the conclusion
  The major premise can no longer be  F\<subseteq>H since we need to reason about G*)

lemma component_guaranteesD: 
     "[| F \<in> X guarantees Y;  F Join G = H;  H \<in> X;  F ok G; G \<in> program |]  
      ==> H \<in> Y"
by (simp add: guar_def, blast)

lemma guarantees_weaken: 
     "[| F \<in> X guarantees X'; Y \<subseteq> X; X' \<subseteq> Y' |] ==> F \<in> Y guarantees Y'"
by (simp add: guar_def, auto)

lemma subset_imp_guarantees_program:
     "X \<subseteq> Y ==> X guarantees Y = program"
by (unfold guar_def, blast)

(*Equivalent to subset_imp_guarantees_UNIV but more intuitive*)
lemma subset_imp_guarantees:
     "[| X \<subseteq> Y; F \<in> program |] ==> F \<in> X guarantees Y"
by (unfold guar_def, blast)

lemma component_of_Join1: "F ok G ==> F component_of (F Join G)"
by (unfold component_of_def, blast)

lemma component_of_Join2: "F ok G ==> G component_of (F Join G)"
apply (subst Join_commute)
apply (blast intro: ok_sym component_of_Join1)
done

(*Remark at end of section 4.1 *)
lemma ex_prop_imp: 
     "ex_prop(Y) ==> (Y = (program guarantees Y))"
apply (simp (no_asm_use) add: ex_prop_equiv guar_def component_of_def)
apply clarify
apply (rule equalityI, blast, safe)
apply (drule_tac x = x in bspec, assumption, force) 
done

lemma guarantees_imp: "(Y = program guarantees Y) ==> ex_prop(Y)"
apply (unfold guar_def)
apply (simp (no_asm_simp) add: ex_prop_equiv)
apply safe
apply (blast intro: elim: equalityE) 
apply (simp_all (no_asm_use) add: component_of_def)
apply (force elim: equalityE)+
done

lemma ex_prop_equiv2: "(ex_prop(Y)) <-> (Y = program guarantees Y)"
by (blast intro: ex_prop_imp guarantees_imp)

(** Distributive laws.  Re-orient to perform miniscoping **)

lemma guarantees_UN_left: 
     "i \<in> I ==>(\<Union>i \<in> I. X(i)) guarantees Y = (\<Inter>i \<in> I. X(i) guarantees Y)"
apply (unfold guar_def)
apply (rule equalityI, safe)
 prefer 2 apply force
apply blast+
done

lemma guarantees_Un_left: 
     "(X Un Y) guarantees Z = (X guarantees Z) Int (Y guarantees Z)"
apply (unfold guar_def)
apply (rule equalityI, safe, blast+)
done

lemma guarantees_INT_right: 
     "i \<in> I ==> X guarantees (\<Inter>i \<in> I. Y(i)) = (\<Inter>i \<in> I. X guarantees Y(i))"
apply (unfold guar_def)
apply (rule equalityI, safe, blast+)
done

lemma guarantees_Int_right: 
     "Z guarantees (X Int Y) = (Z guarantees X) Int (Z guarantees Y)"
by (unfold guar_def, blast)

lemma guarantees_Int_right_I:
     "[| F \<in> Z guarantees X;  F \<in> Z guarantees Y |]  
     ==> F \<in> Z guarantees (X Int Y)"
by (simp (no_asm_simp) add: guarantees_Int_right)

lemma guarantees_INT_right_iff:
     "i \<in> I==> (F \<in> X guarantees (\<Inter>i \<in> I. Y(i))) <->  
      (\<forall>i \<in> I. F \<in> X guarantees Y(i))"
by (simp add: guarantees_INT_right INT_iff, blast)


lemma shunting: "(X guarantees Y) = (program guarantees ((program-X) Un Y))"
by (unfold guar_def, auto)

lemma contrapositive:
     "(X guarantees Y) = (program - Y) guarantees (program -X)"
by (unfold guar_def, blast)

(** The following two can be expressed using intersection and subset, which
    is more faithful to the text but looks cryptic.
**)

lemma combining1: 
    "[| F \<in> V guarantees X;  F \<in> (X Int Y) guarantees Z |] 
     ==> F \<in> (V Int Y) guarantees Z"
by (unfold guar_def, blast)

lemma combining2: 
    "[| F \<in> V guarantees (X Un Y);  F \<in> Y guarantees Z |] 
     ==> F \<in> V guarantees (X Un Z)"
by (unfold guar_def, blast)


(** The following two follow Chandy-Sanders, but the use of object-quantifiers
    does not suit Isabelle... **)

(*Premise should be (!!i. i \<in> I ==> F \<in> X guarantees Y i) *)
lemma all_guarantees: 
     "[| \<forall>i \<in> I. F \<in> X guarantees Y(i); i \<in> I |]  
    ==> F \<in> X guarantees (\<Inter>i \<in> I. Y(i))"
by (unfold guar_def, blast)

(*Premises should be [| F \<in> X guarantees Y i; i \<in> I |] *)
lemma ex_guarantees: 
     "\<exists>i \<in> I. F \<in> X guarantees Y(i) ==> F \<in> X guarantees (\<Union>i \<in> I. Y(i))"
by (unfold guar_def, blast)


(*** Additional guarantees laws, by lcp ***)

lemma guarantees_Join_Int: 
    "[| F \<in> U guarantees V;  G \<in> X guarantees Y; F ok G |]  
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
    "[| F \<in> U guarantees V;  G \<in> X guarantees Y; F ok G |]   
     ==> F Join G: (U Un X) guarantees (V Un Y)"
apply (unfold guar_def)
apply (simp (no_asm))
apply safe
apply (simp add: Join_assoc)
apply (subgoal_tac "F Join G Join Ga = G Join (F Join Ga) ")
apply (rotate_tac 4)
apply (drule_tac x = "F Join Ga" in bspec)
apply (simp (no_asm))
apply (force simp add: ok_commute)
apply (simp (no_asm_simp) add: Join_ac)
done

lemma guarantees_JN_INT: 
     "[| \<forall>i \<in> I. F(i) \<in> X(i) guarantees Y(i);  OK(I,F); i \<in> I |]  
      ==> (\<Squnion>i \<in> I. F(i)) \<in> (\<Inter>i \<in> I. X(i)) guarantees (\<Inter>i \<in> I. Y(i))"
apply (unfold guar_def, safe)
 prefer 2 apply blast
apply (drule_tac x = xa in bspec)
apply (simp_all add: INT_iff, safe)
apply (drule_tac x = "(\<Squnion>x \<in> (I-{xa}) . F (x)) Join G" and A=program in bspec)
apply (auto intro: OK_imp_ok simp add: Join_assoc [symmetric] JN_Join_diff JN_absorb)
done

lemma guarantees_JN_UN: 
    "[| \<forall>i \<in> I. F(i) \<in> X(i) guarantees Y(i);  OK(I,F) |]  
     ==> JOIN(I,F) \<in> (\<Union>i \<in> I. X(i)) guarantees (\<Union>i \<in> I. Y(i))"
apply (unfold guar_def, auto)
apply (drule_tac x = y in bspec, simp_all, safe)
apply (rename_tac G y)
apply (drule_tac x = "JOIN (I-{y}, F) Join G" and A=program in bspec)
apply (auto intro: OK_imp_ok simp add: Join_assoc [symmetric] JN_Join_diff JN_absorb)
done

(*** guarantees laws for breaking down the program, by lcp ***)

lemma guarantees_Join_I1: 
     "[| F \<in> X guarantees Y;  F ok G |] ==> F Join G \<in> X guarantees Y"
apply (simp add: guar_def, safe)
apply (simp add: Join_assoc)
done

lemma guarantees_Join_I2:
     "[| G \<in> X guarantees Y;  F ok G |] ==> F Join G \<in> X guarantees Y"
apply (simp add: Join_commute [of _ G] ok_commute [of _ G])
apply (blast intro: guarantees_Join_I1)
done

lemma guarantees_JN_I: 
     "[| i \<in> I; F(i) \<in>  X guarantees Y;  OK(I,F) |]  
      ==> (\<Squnion>i \<in> I. F(i)) \<in> X guarantees Y"
apply (unfold guar_def, safe)
apply (drule_tac x = "JOIN (I-{i},F) Join G" in bspec)
apply (simp (no_asm))
apply (auto intro: OK_imp_ok simp add: JN_Join_diff Join_assoc [symmetric])
done

(*** well-definedness ***)

lemma Join_welldef_D1: "F Join G \<in> welldef ==> programify(F) \<in>  welldef"
by (unfold welldef_def, auto)

lemma Join_welldef_D2: "F Join G \<in> welldef ==> programify(G) \<in>  welldef"
by (unfold welldef_def, auto)

(*** refinement ***)

lemma refines_refl: "F refines F wrt X"
by (unfold refines_def, blast)

(* More results on guarantees, added by Sidi Ehmety from Chandy & Sander, section 6 *)

lemma wg_type: "wg(F, X) \<subseteq> program"
by (unfold wg_def, auto)

lemma guarantees_type: "X guarantees Y \<subseteq> program"
by (unfold guar_def, auto)

lemma wgD2: "G \<in> wg(F, X) ==> G \<in> program & F \<in> program"
apply (unfold wg_def, auto)
apply (blast dest: guarantees_type [THEN subsetD])
done

lemma guarantees_equiv: 
"(F \<in> X guarantees Y) <->  
   F \<in> program & (\<forall>H \<in> program. H \<in> X --> (F component_of H --> H \<in> Y))"
by (unfold guar_def component_of_def, force) 

lemma wg_weakest:
     "!!X. [| F \<in> (X guarantees Y); X \<subseteq> program |] ==> X \<subseteq> wg(F,Y)"
by (unfold wg_def, auto)

lemma wg_guarantees: "F \<in> program ==> F \<in> wg(F,Y) guarantees Y"
by (unfold wg_def guar_def, blast)

lemma wg_equiv:
     "H \<in> wg(F,X) <-> 
      ((F component_of H --> H \<in> X) & F \<in> program & H \<in> program)"
apply (simp add: wg_def guarantees_equiv)
apply (rule iffI, safe)
apply (rule_tac [4] x = "{H}" in bexI)
apply (rule_tac [3] x = "{H}" in bexI, blast+)
done

lemma component_of_wg: 
    "F component_of H ==> H \<in> wg(F,X) <-> (H \<in> X & F \<in> program & H \<in> program)"
by (simp (no_asm_simp) add: wg_equiv)

lemma wg_finite [rule_format]: 
"\<forall>FF \<in> Fin(program). FF Int X \<noteq> 0 --> OK(FF, %F. F)  
   --> (\<forall>F \<in> FF. ((\<Squnion>F \<in> FF. F) \<in>  wg(F,X)) <-> ((\<Squnion>F \<in> FF. F) \<in> X))"
apply clarify
apply (subgoal_tac "F component_of (\<Squnion>F \<in> FF. F) ")
apply (drule_tac X = X in component_of_wg)
apply (force dest!: Fin.dom_subset [THEN subsetD, THEN PowD])
apply (simp_all add: component_of_def)
apply (rule_tac x = "\<Squnion>F \<in> (FF-{F}) . F" in exI)
apply (auto intro: JN_Join_diff dest: ok_sym simp add: OK_iff_ok)
done

lemma wg_ex_prop:
     "ex_prop(X) ==> (F \<in> X) <-> (\<forall>H \<in> program. H \<in> wg(F,X) & F \<in> program)"
apply (simp (no_asm_use) add: ex_prop_equiv wg_equiv)
apply blast
done

(** From Charpentier and Chandy "Theorems About Composition" **)
(* Proposition 2 *)
lemma wx_subset: "wx(X)\<subseteq>X"
by (unfold wx_def, auto)

lemma wx_ex_prop: "ex_prop(wx(X))"
apply (simp (no_asm_use) add: ex_prop_def wx_def)
apply safe
apply blast
apply (rule_tac x=x in bexI, force, simp)+
done

lemma wx_weakest: "\<forall>Z. Z\<subseteq>program --> Z\<subseteq> X --> ex_prop(Z) --> Z \<subseteq> wx(X)"
by (unfold wx_def, auto)

(* Proposition 6 *)
lemma wx'_ex_prop: 
 "ex_prop({F \<in> program. \<forall>G \<in> program. F ok G --> F Join G \<in> X})"
apply (unfold ex_prop_def, safe)
 apply (drule_tac x = "G Join Ga" in bspec)
  apply (simp (no_asm))
 apply (force simp add: Join_assoc)
apply (drule_tac x = "F Join Ga" in bspec)
 apply (simp (no_asm))
apply (simp (no_asm_use))
apply safe
 apply (simp (no_asm_simp) add: ok_commute)
apply (subgoal_tac "F Join G = G Join F")
 apply (simp (no_asm_simp) add: Join_assoc)
apply (simp (no_asm) add: Join_commute)
done

(* Equivalence with the other definition of wx *)

lemma wx_equiv: 
     "wx(X) = {F \<in> program. \<forall>G \<in> program. F ok G --> (F Join G) \<in> X}"
apply (unfold wx_def)
apply (rule equalityI, safe, blast)
 apply (simp (no_asm_use) add: ex_prop_def)
apply blast 
apply (rule_tac B = "{F \<in> program. \<forall>G \<in> program. F ok G --> F Join G \<in> X}" 
         in UnionI, 
       safe)
apply (rule_tac [2] wx'_ex_prop)
apply (drule_tac x=SKIP in bspec, simp)+
apply auto 
done

(* Propositions 7 to 11 are all about this second definition of wx. And
   by equivalence between the two definition, they are the same as the ones proved *)


(* Proposition 12 *)
(* Main result of the paper *)
lemma guarantees_wx_eq: "(X guarantees Y) = wx((program-X) Un Y)"
by (auto simp add: guar_def wx_equiv)

(* 
{* Corollary, but this result has already been proved elsewhere *}
 "ex_prop(X guarantees Y)"
*)

(* Rules given in section 7 of Chandy and Sander's
    Reasoning About Program composition paper *)

lemma stable_guarantees_Always:
     "[| Init(F) \<subseteq> A; F \<in> program |] ==> F \<in> stable(A) guarantees Always(A)"
apply (rule guaranteesI)
 prefer 2 apply assumption
apply (simp (no_asm) add: Join_commute)
apply (rule stable_Join_Always1)
apply (simp_all add: invariant_def)
apply (auto simp add: programify_def initially_def)
done

lemma constrains_guarantees_leadsTo:
     "[| F \<in> transient(A); st_set(B) |] 
      ==> F: (A co A Un B) guarantees (A leadsTo (B-A))"
apply (rule guaranteesI)
 prefer 2 apply (blast dest: transient_type [THEN subsetD])
apply (rule leadsTo_Basis')
  apply (blast intro: constrains_weaken_R) 
 apply (blast intro!: Join_transient_I1, blast)
done

end
