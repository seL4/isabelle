(*  Title:      HOL/UNITY/Reachability
    ID:         $Id$
    Author:     Tanja Vos, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Reachability in Graphs

From Chandy and Misra, "Parallel Program Design" (1989), sections 6.2 and 11.3
*)

theory Reachability = Detects + Reach:

types  edge = "(vertex*vertex)"

record state =
  reach :: "vertex => bool"
  nmsg  :: "edge => nat"

consts REACHABLE :: "edge set"
       root :: "vertex"
       E :: "edge set"
       V :: "vertex set"

inductive "REACHABLE"
  intros
   base: "v : V ==> ((v,v) : REACHABLE)"
   step: "((u,v) : REACHABLE) & (v,w) : E ==> ((u,w) : REACHABLE)"

constdefs
  reachable :: "vertex => state set"
  "reachable p == {s. reach s p}"

  nmsg_eq :: "nat => edge  => state set"
  "nmsg_eq k == %e. {s. nmsg s e = k}"

  nmsg_gt :: "nat => edge  => state set"
  "nmsg_gt k  == %e. {s. k < nmsg s e}"

  nmsg_gte :: "nat => edge => state set"
  "nmsg_gte k == %e. {s. k <= nmsg s e}"

  nmsg_lte  :: "nat => edge => state set"
  "nmsg_lte k  == %e. {s. nmsg s e <= k}"

  

  final :: "state set"
  "final == (INTER V (%v. reachable v <==> {s. (root, v) : REACHABLE})) Int (INTER E (nmsg_eq 0))"

axioms

    Graph1: "root : V"

    Graph2: "(v,w) : E ==> (v : V) & (w : V)"

    MA1:  "F : Always (reachable root)"

    MA2:  "v: V ==> F : Always (- reachable v Un {s. ((root,v) : REACHABLE)})"

    MA3:  "[|v:V;w:V|] ==> F : Always (-(nmsg_gt 0 (v,w)) Un (reachable v))"

    MA4:  "(v,w) : E ==> 
           F : Always (-(reachable v) Un (nmsg_gt 0 (v,w)) Un (reachable w))"

    MA5:  "[|v:V; w:V|] 
           ==> F : Always (nmsg_gte 0 (v,w) Int nmsg_lte (Suc 0) (v,w))"

    MA6:  "[|v:V|] ==> F : Stable (reachable v)"

    MA6b: "[|v:V;w:W|] ==> F : Stable (reachable v Int nmsg_lte k (v,w))"

    MA7:  "[|v:V;w:V|] ==> F : UNIV LeadsTo nmsg_eq 0 (v,w)"


lemmas E_imp_in_V_L = Graph2 [THEN conjunct1, standard]
lemmas E_imp_in_V_R = Graph2 [THEN conjunct2, standard]

lemma lemma2:
     "(v,w) : E ==> F : reachable v LeadsTo nmsg_eq 0 (v,w) Int reachable v"
apply (rule MA7 [THEN PSP_Stable, THEN LeadsTo_weaken_L])
apply (rule_tac [3] MA6)
apply (auto simp add: E_imp_in_V_L E_imp_in_V_R)
done

lemma Induction_base: "(v,w) : E ==> F : reachable v LeadsTo reachable w"
apply (rule MA4 [THEN Always_LeadsTo_weaken])
apply (rule_tac [2] lemma2)
apply (auto simp add: nmsg_eq_def nmsg_gt_def)
done

lemma REACHABLE_LeadsTo_reachable:
     "(v,w) : REACHABLE ==> F : reachable v LeadsTo reachable w"
apply (erule REACHABLE.induct)
apply (rule subset_imp_LeadsTo, blast)
apply (blast intro: LeadsTo_Trans Induction_base)
done

lemma Detects_part1: "F : {s. (root,v) : REACHABLE} LeadsTo reachable v"
apply (rule single_LeadsTo_I)
apply (simp split add: split_if_asm)
apply (rule MA1 [THEN Always_LeadsToI])
apply (erule REACHABLE_LeadsTo_reachable [THEN LeadsTo_weaken_L], auto)
done


lemma Reachability_Detected: 
     "v : V ==> F : (reachable v) Detects {s. (root,v) : REACHABLE}"
apply (unfold Detects_def, auto)
 prefer 2 apply (blast intro: MA2 [THEN Always_weaken])
apply (rule Detects_part1 [THEN LeadsTo_weaken_L], blast)
done


lemma LeadsTo_Reachability:
     "v : V ==> F : UNIV LeadsTo (reachable v <==> {s. (root,v) : REACHABLE})"
by (erule Reachability_Detected [THEN Detects_Imp_LeadstoEQ])


(* ------------------------------------ *)

(* Some lemmas about <==> *)

lemma Eq_lemma1: 
     "(reachable v <==> {s. (root,v) : REACHABLE}) =  
      {s. ((s : reachable v) = ((root,v) : REACHABLE))}"
apply (unfold Equality_def, blast)
done


lemma Eq_lemma2: 
     "(reachable v <==> (if (root,v) : REACHABLE then UNIV else {})) =  
      {s. ((s : reachable v) = ((root,v) : REACHABLE))}"
apply (unfold Equality_def, auto)
done

(* ------------------------------------ *)


(* Some lemmas about final (I don't need all of them!)  *)

lemma final_lemma1: 
     "(INT v: V. INT w:V. {s. ((s : reachable v) = ((root,v) : REACHABLE)) &  
                              s : nmsg_eq 0 (v,w)})  
      <= final"
apply (unfold final_def Equality_def, auto)
apply (frule E_imp_in_V_R)
apply (frule E_imp_in_V_L, blast)
done

lemma final_lemma2: 
 "E~={}  
  ==> (INT v: V. INT e: E. {s. ((s : reachable v) = ((root,v) : REACHABLE))}  
                           Int nmsg_eq 0 e)    <=  final"
apply (unfold final_def Equality_def)
apply (auto split add: split_if_asm)
apply (frule E_imp_in_V_L, blast)
done

lemma final_lemma3:
     "E~={}  
      ==> (INT v: V. INT e: E.  
           (reachable v <==> {s. (root,v) : REACHABLE}) Int nmsg_eq 0 e)  
          <= final"
apply (frule final_lemma2)
apply (simp (no_asm_use) add: Eq_lemma2)
done


lemma final_lemma4:
     "E~={}  
      ==> (INT v: V. INT e: E.  
           {s. ((s : reachable v) = ((root,v) : REACHABLE))} Int nmsg_eq 0 e)  
          = final"
apply (rule subset_antisym)
apply (erule final_lemma2)
apply (unfold final_def Equality_def, blast)
done

lemma final_lemma5:
     "E~={}  
      ==> (INT v: V. INT e: E.  
           ((reachable v) <==> {s. (root,v) : REACHABLE}) Int nmsg_eq 0 e)  
          = final"
apply (frule final_lemma4)
apply (simp (no_asm_use) add: Eq_lemma2)
done


lemma final_lemma6:
     "(INT v: V. INT w: V.  
       (reachable v <==> {s. (root,v) : REACHABLE}) Int nmsg_eq 0 (v,w))  
      <= final"
apply (simp (no_asm) add: Eq_lemma2 Int_def)
apply (rule final_lemma1)
done


lemma final_lemma7: 
     "final =  
      (INT v: V. INT w: V.  
       ((reachable v) <==> {s. (root,v) : REACHABLE}) Int  
       (-{s. (v,w) : E} Un (nmsg_eq 0 (v,w))))"
apply (unfold final_def)
apply (rule subset_antisym, blast)
apply (auto split add: split_if_asm)
apply (blast dest: E_imp_in_V_L E_imp_in_V_R)+
done

(* ------------------------------------ *)


(* ------------------------------------ *)

(* Stability theorems *)
lemma not_REACHABLE_imp_Stable_not_reachable:
     "[| v : V; (root,v) ~: REACHABLE |] ==> F : Stable (- reachable v)"
apply (drule MA2 [THEN AlwaysD], auto)
done

lemma Stable_reachable_EQ_R:
     "v : V ==> F : Stable (reachable v <==> {s. (root,v) : REACHABLE})"
apply (simp (no_asm) add: Equality_def Eq_lemma2)
apply (blast intro: MA6 not_REACHABLE_imp_Stable_not_reachable)
done


lemma lemma4: 
     "((nmsg_gte 0 (v,w) Int nmsg_lte (Suc 0) (v,w)) Int 
       (- nmsg_gt 0 (v,w) Un A))  
      <= A Un nmsg_eq 0 (v,w)"
apply (unfold nmsg_gte_def nmsg_lte_def nmsg_gt_def nmsg_eq_def, auto)
done


lemma lemma5: 
     "reachable v Int nmsg_eq 0 (v,w) =  
      ((nmsg_gte 0 (v,w) Int nmsg_lte (Suc 0) (v,w)) Int  
       (reachable v Int nmsg_lte 0 (v,w)))"
apply (unfold nmsg_gte_def nmsg_lte_def nmsg_gt_def nmsg_eq_def, auto)
done

lemma lemma6: 
     "- nmsg_gt 0 (v,w) Un reachable v <= nmsg_eq 0 (v,w) Un reachable v"
apply (unfold nmsg_gte_def nmsg_lte_def nmsg_gt_def nmsg_eq_def, auto)
done

lemma Always_reachable_OR_nmsg_0:
     "[|v : V; w : V|] ==> F : Always (reachable v Un nmsg_eq 0 (v,w))"
apply (rule Always_Int_I [OF MA5 MA3, THEN Always_weaken])
apply (rule_tac [5] lemma4, auto)
done

lemma Stable_reachable_AND_nmsg_0:
     "[|v : V; w : V|] ==> F : Stable (reachable v Int nmsg_eq 0 (v,w))"
apply (subst lemma5)
apply (blast intro: MA5 Always_imp_Stable [THEN Stable_Int] MA6b)
done

lemma Stable_nmsg_0_OR_reachable:
     "[|v : V; w : V|] ==> F : Stable (nmsg_eq 0 (v,w) Un reachable v)"
by (blast intro!: Always_weaken [THEN Always_imp_Stable] lemma6 MA3)

lemma not_REACHABLE_imp_Stable_not_reachable_AND_nmsg_0:
     "[| v : V; w:V; (root,v) ~: REACHABLE |]  
      ==> F : Stable (- reachable v Int nmsg_eq 0 (v,w))"
apply (rule Stable_Int [OF MA2 [THEN Always_imp_Stable] 
                           Stable_nmsg_0_OR_reachable, 
            THEN Stable_eq])
   prefer 4 apply blast
apply auto
done

lemma Stable_reachable_EQ_R_AND_nmsg_0:
     "[| v : V; w:V |]  
      ==> F : Stable ((reachable v <==> {s. (root,v) : REACHABLE}) Int  
                      nmsg_eq 0 (v,w))"
by (simp add: Equality_def Eq_lemma2  Stable_reachable_AND_nmsg_0
              not_REACHABLE_imp_Stable_not_reachable_AND_nmsg_0)



(* ------------------------------------ *)


(* LeadsTo final predicate (Exercise 11.2 page 274) *)

lemma UNIV_lemma: "UNIV <= (INT v: V. UNIV)"
by blast

lemmas UNIV_LeadsTo_completion = 
    LeadsTo_weaken_L [OF Finite_stable_completion UNIV_lemma]

lemma LeadsTo_final_E_empty: "E={} ==> F : UNIV LeadsTo final"
apply (unfold final_def, simp)
apply (rule UNIV_LeadsTo_completion)
  apply safe
 apply (erule LeadsTo_Reachability [simplified])
apply (drule Stable_reachable_EQ_R, simp)
done


lemma Leadsto_reachability_AND_nmsg_0:
     "[| v : V; w:V |]  
      ==> F : UNIV LeadsTo  
             ((reachable v <==> {s. (root,v): REACHABLE}) Int nmsg_eq 0 (v,w))"
apply (rule LeadsTo_Reachability [THEN LeadsTo_Trans], blast)
apply (subgoal_tac
	 "F : (reachable v <==> {s. (root,v) : REACHABLE}) Int 
              UNIV LeadsTo (reachable v <==> {s. (root,v) : REACHABLE}) Int 
              nmsg_eq 0 (v,w) ")
apply simp
apply (rule PSP_Stable2)
apply (rule MA7)
apply (rule_tac [3] Stable_reachable_EQ_R, auto)
done

lemma LeadsTo_final_E_NOT_empty: "E~={} ==> F : UNIV LeadsTo final"
apply (rule LeadsTo_weaken_L [OF LeadsTo_weaken_R UNIV_lemma])
apply (rule_tac [2] final_lemma6)
apply (rule Finite_stable_completion)
  apply blast
 apply (rule UNIV_LeadsTo_completion)
   apply (blast intro: Stable_INT Stable_reachable_EQ_R_AND_nmsg_0
                    Leadsto_reachability_AND_nmsg_0)+
done

lemma LeadsTo_final: "F : UNIV LeadsTo final"
apply (case_tac "E={}")
apply (rule_tac [2] LeadsTo_final_E_NOT_empty)
apply (rule LeadsTo_final_E_empty, auto)
done

(* ------------------------------------ *)

(* Stability of final (Exercise 11.2 page 274) *)

lemma Stable_final_E_empty: "E={} ==> F : Stable final"
apply (unfold final_def, simp)
apply (rule Stable_INT)
apply (drule Stable_reachable_EQ_R, simp)
done


lemma Stable_final_E_NOT_empty: "E~={} ==> F : Stable final"
apply (subst final_lemma7)
apply (rule Stable_INT)
apply (rule Stable_INT)
apply (simp (no_asm) add: Eq_lemma2)
apply safe
apply (rule Stable_eq)
apply (subgoal_tac [2] "({s. (s : reachable v) = ((root,v) : REACHABLE) } Int nmsg_eq 0 (v,w)) = ({s. (s : reachable v) = ( (root,v) : REACHABLE) } Int (- UNIV Un nmsg_eq 0 (v,w))) ")
prefer 2 apply blast 
prefer 2 apply blast 
apply (rule Stable_reachable_EQ_R_AND_nmsg_0
            [simplified Eq_lemma2 Collect_const])
apply (blast, blast)
apply (rule Stable_eq)
 apply (rule Stable_reachable_EQ_R [simplified Eq_lemma2 Collect_const])
 apply simp
apply (subgoal_tac 
        "({s. (s : reachable v) = ((root,v) : REACHABLE) }) = 
         ({s. (s : reachable v) = ( (root,v) : REACHABLE) } Int
              (- {} Un nmsg_eq 0 (v,w)))")
apply blast+
done

lemma Stable_final: "F : Stable final"
apply (case_tac "E={}")
prefer 2 apply (blast intro: Stable_final_E_NOT_empty)
apply (blast intro: Stable_final_E_empty)
done

end

