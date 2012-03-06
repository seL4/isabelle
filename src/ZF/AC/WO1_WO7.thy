(*  Title:      ZF/AC/WO1_WO7.thy
    Author:     Lawrence C Paulson, CU Computer Laboratory
    Copyright   1998  University of Cambridge

WO7 \<longleftrightarrow> LEMMA \<longleftrightarrow> WO1 (Rubin & Rubin p. 5)
LEMMA is the sentence denoted by (**)

Also, WO1 \<longleftrightarrow> WO8
*)

theory WO1_WO7
imports AC_Equiv
begin

definition
    "LEMMA ==
     \<forall>X. ~Finite(X) \<longrightarrow> (\<exists>R. well_ord(X,R) & ~well_ord(X,converse(R)))"

(* ********************************************************************** *)
(* It is easy to see that WO7 is equivalent to (**)                       *)
(* ********************************************************************** *)

lemma WO7_iff_LEMMA: "WO7 \<longleftrightarrow> LEMMA"
apply (unfold WO7_def LEMMA_def)
apply (blast intro: Finite_well_ord_converse)
done

(* ********************************************************************** *)
(* It is also easy to show that LEMMA implies WO1.                        *)
(* ********************************************************************** *)

lemma LEMMA_imp_WO1: "LEMMA ==> WO1"
apply (unfold WO1_def LEMMA_def Finite_def eqpoll_def)
apply (blast intro!: well_ord_rvimage [OF bij_is_inj nat_implies_well_ord])
done

(* ********************************************************************** *)
(* The Rubins' proof of the other implication is contained within the     *)
(* following sentence \<in>                                                   *)
(* "... each infinite ordinal is well ordered by < but not by >."         *)
(* This statement can be proved by the following two theorems.            *)
(* But moreover we need to show similar property for any well ordered     *)
(* infinite set. It is not very difficult thanks to Isabelle order types  *)
(* We show that if a set is well ordered by some relation and by its     *)
(* converse, then apropriate order type is well ordered by the converse   *)
(* of it's membership relation, which in connection with the previous     *)
(* gives the conclusion.                                                  *)
(* ********************************************************************** *)

lemma converse_Memrel_not_wf_on: 
    "[| Ord(a); ~Finite(a) |] ==> ~wf[a](converse(Memrel(a)))"
apply (unfold wf_on_def wf_def)
apply (drule nat_le_infinite_Ord [THEN le_imp_subset], assumption)
apply (rule notI)
apply (erule_tac x = nat in allE, blast)
done

lemma converse_Memrel_not_well_ord: 
    "[| Ord(a); ~Finite(a) |] ==> ~well_ord(a,converse(Memrel(a)))"
apply (unfold well_ord_def)
apply (blast dest: converse_Memrel_not_wf_on)
done

lemma well_ord_rvimage_ordertype:
     "well_ord(A,r) \<Longrightarrow>
       rvimage (ordertype(A,r), converse(ordermap(A,r)),r) =
       Memrel(ordertype(A,r))" 
by (blast intro: ordertype_ord_iso [THEN ord_iso_sym] ord_iso_rvimage_eq
             Memrel_type [THEN subset_Int_iff [THEN iffD1]] trans)

lemma well_ord_converse_Memrel:
     "[| well_ord(A,r); well_ord(A,converse(r)) |]   
      ==> well_ord(ordertype(A,r), converse(Memrel(ordertype(A,r))))" 
apply (subst well_ord_rvimage_ordertype [symmetric], assumption) 
apply (rule rvimage_converse [THEN subst])
apply (blast intro: ordertype_ord_iso ord_iso_sym ord_iso_is_bij
                    bij_is_inj well_ord_rvimage)
done

lemma WO1_imp_LEMMA: "WO1 ==> LEMMA"
apply (unfold WO1_def LEMMA_def, clarify) 
apply (blast dest: well_ord_converse_Memrel
                   Ord_ordertype [THEN converse_Memrel_not_well_ord]
             intro: ordertype_ord_iso ord_iso_is_bij bij_is_inj lepoll_Finite
                    lepoll_def [THEN def_imp_iff, THEN iffD2] )
done

lemma WO1_iff_WO7: "WO1 \<longleftrightarrow> WO7"
apply (simp add: WO7_iff_LEMMA)
apply (blast intro: LEMMA_imp_WO1 WO1_imp_LEMMA)
done



(* ********************************************************************** *)
(*            The proof of WO8 \<longleftrightarrow> WO1 (Rubin & Rubin p. 6)               *)
(* ********************************************************************** *)

lemma WO1_WO8: "WO1 ==> WO8"
by (unfold WO1_def WO8_def, fast)


(* The implication "WO8 ==> WO1": a faithful image of Rubin & Rubin's proof*)
lemma WO8_WO1: "WO8 ==> WO1"
apply (unfold WO1_def WO8_def)
apply (rule allI)
apply (erule_tac x = "{{x}. x \<in> A}" in allE)
apply (erule impE)
 apply (rule_tac x = "\<lambda>a \<in> {{x}. x \<in> A}. THE x. a={x}" in exI)
 apply (force intro!: lam_type simp add: singleton_eq_iff the_equality)
apply (blast intro: lam_sing_bij bij_is_inj well_ord_rvimage)
done

end
