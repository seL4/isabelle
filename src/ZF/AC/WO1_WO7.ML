(*  Title:      ZF/AC/WO1_WO7.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

WO7 <-> LEMMA <-> WO1 (Rubin & Rubin p. 5)
LEMMA is the sentence denoted by (**)
*)

(* ********************************************************************** *)
(* It is easy to see, that WO7 is equivallent to (**)                     *)
(* ********************************************************************** *)

Goalw [WO7_def, LEMMA_def] 
  "WO7 <-> LEMMA";
by (fast_tac (claset() addSEs [Finite_well_ord_converse]) 1);
qed "WO7_iff_LEMMA";

(* ********************************************************************** *)
(* It is also easy to show that LEMMA implies WO1.                        *)
(* ********************************************************************** *)

Goalw [WO1_def, LEMMA_def] "LEMMA ==> WO1";
by (rtac allI 1);
by (etac allE 1);
by (excluded_middle_tac "Finite(A)" 1);
by (Fast_tac 1);
by (rewrite_goals_tac [Finite_def, eqpoll_def]);
by (fast_tac (claset() addSIs [[bij_is_inj, nat_implies_well_ord] MRS
                                 well_ord_rvimage]) 1);
qed "LEMMA_imp_WO1";

(* ********************************************************************** *)
(* The Rubins' proof of the other implication is contained within the     *)
(* following sentence \\<in>                                                   *)
(* "... each infinite ordinal is well ordered by < but not by >."         *)
(* This statement can be proved by the following two theorems.            *)
(* But moreover we need to show similar property for any well ordered     *)
(* infinite set. It is not very difficult thanks to Isabelle order types  *)
(* We show that if a set is well ordered by some relation and by its     *)
(* converse, then apropriate order type is well ordered by the converse   *)
(* of it's membership relation, which in connection with the previous     *)
(* gives the conclusion.                                                  *)
(* ********************************************************************** *)

Goalw [wf_on_def, wf_def] 
    "[| Ord(a); ~Finite(a) |] ==> ~wf[a](converse(Memrel(a)))";
by (dresolve_tac [nat_le_infinite_Ord RS le_imp_subset] 1 
    THEN (assume_tac 1));
by (rtac notI 1);
by (eres_inst_tac [("x","nat")] allE 1);
by (Blast_tac 1);
qed "converse_Memrel_not_wf_on";

Goalw [well_ord_def] 
    "[| Ord(a); ~Finite(a) |] ==> ~well_ord(a,converse(Memrel(a)))";
by (fast_tac (claset() addSDs [converse_Memrel_not_wf_on]) 1);
qed "converse_Memrel_not_well_ord";

Goal "[| well_ord(A,r); well_ord(A,converse(r)) |]  \
\       ==> well_ord(ordertype(A,r), converse(Memrel(ordertype(A, r))))";
by (rtac ([ordertype_ord_iso RS ord_iso_sym RS ord_iso_rvimage_eq, 
                Memrel_type RS (subset_Int_iff RS iffD1)] 
                MRS trans RS subst) 1
        THEN (assume_tac 1));
by (rtac (rvimage_converse RS subst) 1);
by (etac (ordertype_ord_iso RS ord_iso_sym RS ord_iso_is_bij RS
                bij_is_inj RS well_ord_rvimage) 1
        THEN (assume_tac 1));
qed "well_ord_converse_Memrel";

Goalw [WO1_def, LEMMA_def] "WO1 ==> LEMMA";
by (REPEAT (resolve_tac [allI,impI] 1));
by (REPEAT (eresolve_tac [allE,exE] 1));
by (REPEAT (ares_tac [exI,conjI,notI] 1));
by (ftac well_ord_converse_Memrel 1 THEN (assume_tac 1));
by (forward_tac [Ord_ordertype RS converse_Memrel_not_well_ord] 1);
by (contr_tac 2);
by (fast_tac (empty_cs addSEs [ordertype_ord_iso RS ord_iso_is_bij RS 
                bij_is_inj RS (exI RS (lepoll_def RS def_imp_iff RS iffD2))
                RS lepoll_Finite]
                addSIs [notI] addEs [notE]) 1);
qed "WO1_imp_LEMMA";


Goal "WO1 <-> WO7";
by (simp_tac (simpset() addsimps [WO7_iff_LEMMA]) 1);
by (blast_tac (claset() addIs [LEMMA_imp_WO1, WO1_imp_LEMMA]) 1);
qed "WO1_iff_WO7";
