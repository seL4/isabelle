(*  Title:      HOLCF/IOA/meta_theory/RefCorrectness.thy
    ID:         $Id$
    Author:     Olaf Müller
*)

header {* Correctness of Refinement Mappings in HOLCF/IOA *}

theory RefCorrectness
imports RefMappings
begin

consts

  corresp_ex   ::"('a,'s2)ioa => ('s1 => 's2) =>
                  ('a,'s1)execution => ('a,'s2)execution"
  corresp_exC  ::"('a,'s2)ioa => ('s1 => 's2) => ('a,'s1)pairs
                   -> ('s1 => ('a,'s2)pairs)"
  is_fair_ref_map  :: "('s1 => 's2) => ('a,'s1)ioa => ('a,'s2)ioa => bool"

defs

corresp_ex_def:
  "corresp_ex A f ex == (f (fst ex),(corresp_exC A f$(snd ex)) (fst ex))"


corresp_exC_def:
  "corresp_exC A f  == (fix$(LAM h ex. (%s. case ex of
      nil =>  nil
    | x##xs => (flift1 (%pr. (@cex. move A cex (f s) (fst pr) (f (snd pr)))
                              @@ ((h$xs) (snd pr)))
                        $x) )))"

is_fair_ref_map_def:
  "is_fair_ref_map f C A ==
       is_ref_map f C A &
       (! ex : executions(C). fair_ex C ex --> fair_ex A (corresp_ex A f ex))"



axioms
(* Axioms for fair trace inclusion proof support, not for the correctness proof
   of refinement mappings!
   Note: Everything is superseded by LiveIOA.thy! *)

corresp_laststate:
  "Finite ex ==> laststate (corresp_ex A f (s,ex)) = f (laststate (s,ex))"

corresp_Finite:
  "Finite (snd (corresp_ex A f (s,ex))) = Finite ex"

FromAtoC:
  "fin_often (%x. P (snd x)) (snd (corresp_ex A f (s,ex))) ==> fin_often (%y. P (f (snd y))) ex"

FromCtoA:
  "inf_often (%y. P (fst y)) ex ==> inf_often (%x. P (fst x)) (snd (corresp_ex A f (s,ex)))"


(* Proof by case on inf W in ex: If so, ok. If not, only fin W in ex, ie there is
   an index i from which on no W in ex. But W inf enabled, ie at least once after i
   W is enabled. As W does not occur after i and W is enabling_persistent, W keeps
   enabled until infinity, ie. indefinitely *)
persistent:
  "[|inf_often (%x. Enabled A W (snd x)) ex; en_persistent A W|]
   ==> inf_often (%x. fst x :W) ex | fin_often (%x. ~Enabled A W (snd x)) ex"

infpostcond:
  "[| is_exec_frag A (s,ex); inf_often (%x. fst x:W) ex|]
    ==> inf_often (% x. set_was_enabled A W (snd x)) ex"


subsection "corresp_ex"

lemma corresp_exC_unfold: "corresp_exC A f  = (LAM ex. (%s. case ex of  
       nil =>  nil    
     | x##xs => (flift1 (%pr. (@cex. move A cex (f s) (fst pr) (f (snd pr)))    
                               @@ ((corresp_exC A f $xs) (snd pr)))    
                         $x) ))"
apply (rule trans)
apply (rule fix_eq2)
apply (rule corresp_exC_def)
apply (rule beta_cfun)
apply (simp add: flift1_def)
done

lemma corresp_exC_UU: "(corresp_exC A f$UU) s=UU"
apply (subst corresp_exC_unfold)
apply simp
done

lemma corresp_exC_nil: "(corresp_exC A f$nil) s = nil"
apply (subst corresp_exC_unfold)
apply simp
done

lemma corresp_exC_cons: "(corresp_exC A f$(at>>xs)) s =  
           (@cex. move A cex (f s) (fst at) (f (snd at)))   
           @@ ((corresp_exC A f$xs) (snd at))"
apply (rule trans)
apply (subst corresp_exC_unfold)
apply (simp add: Consq_def flift1_def)
apply simp
done


declare corresp_exC_UU [simp] corresp_exC_nil [simp] corresp_exC_cons [simp]



subsection "properties of move"

lemma move_is_move: 
   "[|is_ref_map f C A; reachable C s; (s,a,t):trans_of C|] ==> 
      move A (@x. move A x (f s) a (f t)) (f s) a (f t)"
apply (unfold is_ref_map_def)
apply (subgoal_tac "? ex. move A ex (f s) a (f t) ")
prefer 2
apply simp
apply (erule exE)
apply (rule someI)
apply assumption
done

lemma move_subprop1: 
   "[|is_ref_map f C A; reachable C s; (s,a,t):trans_of C|] ==> 
     is_exec_frag A (f s,@x. move A x (f s) a (f t))"
apply (cut_tac move_is_move)
defer
apply assumption+
apply (simp add: move_def)
done

lemma move_subprop2: 
   "[|is_ref_map f C A; reachable C s; (s,a,t):trans_of C|] ==> 
     Finite ((@x. move A x (f s) a (f t)))"
apply (cut_tac move_is_move)
defer
apply assumption+
apply (simp add: move_def)
done

lemma move_subprop3: 
   "[|is_ref_map f C A; reachable C s; (s,a,t):trans_of C|] ==> 
     laststate (f s,@x. move A x (f s) a (f t)) = (f t)"
apply (cut_tac move_is_move)
defer
apply assumption+
apply (simp add: move_def)
done

lemma move_subprop4: 
   "[|is_ref_map f C A; reachable C s; (s,a,t):trans_of C|] ==> 
      mk_trace A$((@x. move A x (f s) a (f t))) =  
        (if a:ext A then a>>nil else nil)"
apply (cut_tac move_is_move)
defer
apply assumption+
apply (simp add: move_def)
done


(* ------------------------------------------------------------------ *)
(*                   The following lemmata contribute to              *)
(*                 TRACE INCLUSION Part 1: Traces coincide            *)
(* ------------------------------------------------------------------ *)

section "Lemmata for <=="

(* --------------------------------------------------- *)
(*   Lemma 1.1: Distribution of mk_trace and @@        *)
(* --------------------------------------------------- *)

lemma mk_traceConc: "mk_trace C$(ex1 @@ ex2)= (mk_trace C$ex1) @@ (mk_trace C$ex2)"
apply (simp add: mk_trace_def filter_act_def FilterConc MapConc)
done



(* ------------------------------------------------------
                 Lemma 1 :Traces coincide
   ------------------------------------------------------- *)
declare split_if [split del]

lemma lemma_1: 
  "[|is_ref_map f C A; ext C = ext A|] ==>   
         !s. reachable C s & is_exec_frag C (s,xs) -->  
             mk_trace C$xs = mk_trace A$(snd (corresp_ex A f (s,xs)))"
apply (unfold corresp_ex_def)
apply (tactic {* pair_induct_tac "xs" [thm "is_exec_frag_def"] 1 *})
(* cons case *)
apply (tactic "safe_tac set_cs")
apply (simp add: mk_traceConc)
apply (frule reachable.reachable_n)
apply assumption
apply (erule_tac x = "y" in allE)
apply simp
apply (simp add: move_subprop4 split add: split_if)
done

declare split_if [split]

(* ------------------------------------------------------------------ *)
(*                   The following lemmata contribute to              *)
(*              TRACE INCLUSION Part 2: corresp_ex is execution       *)
(* ------------------------------------------------------------------ *)

section "Lemmata for ==>"

(* -------------------------------------------------- *)
(*                   Lemma 2.1                        *)
(* -------------------------------------------------- *)

lemma lemma_2_1 [rule_format (no_asm)]: 
"Finite xs -->  
 (!s .is_exec_frag A (s,xs) & is_exec_frag A (t,ys) &  
      t = laststate (s,xs)  
  --> is_exec_frag A (s,xs @@ ys))"

apply (rule impI)
apply (tactic {* Seq_Finite_induct_tac 1 *})
(* main case *)
apply (tactic "safe_tac set_cs")
apply (tactic {* pair_tac "a" 1 *})
done


(* ----------------------------------------------------------- *)
(*               Lemma 2 : corresp_ex is execution             *)
(* ----------------------------------------------------------- *)



lemma lemma_2: 
 "[| is_ref_map f C A |] ==> 
  !s. reachable C s & is_exec_frag C (s,xs)  
  --> is_exec_frag A (corresp_ex A f (s,xs))"

apply (unfold corresp_ex_def)

apply simp
apply (tactic {* pair_induct_tac "xs" [thm "is_exec_frag_def"] 1 *})
(* main case *)
apply (tactic "safe_tac set_cs")
apply (rule_tac t = "f y" in lemma_2_1)

(* Finite *)
apply (erule move_subprop2)
apply assumption+
apply (rule conjI)

(* is_exec_frag *)
apply (erule move_subprop1)
apply assumption+
apply (rule conjI)

(* Induction hypothesis  *)
(* reachable_n looping, therefore apply it manually *)
apply (erule_tac x = "y" in allE)
apply simp
apply (frule reachable.reachable_n)
apply assumption
apply simp
(* laststate *)
apply (erule move_subprop3 [symmetric])
apply assumption+
done


subsection "Main Theorem: TRACE - INCLUSION"

lemma trace_inclusion: 
  "[| ext C = ext A; is_ref_map f C A |]  
           ==> traces C <= traces A"

  apply (unfold traces_def)

  apply (simp (no_asm) add: has_trace_def2)
  apply (tactic "safe_tac set_cs")

  (* give execution of abstract automata *)
  apply (rule_tac x = "corresp_ex A f ex" in bexI)

  (* Traces coincide, Lemma 1 *)
  apply (tactic {* pair_tac "ex" 1 *})
  apply (erule lemma_1 [THEN spec, THEN mp])
  apply assumption+
  apply (simp add: executions_def reachable.reachable_0)

  (* corresp_ex is execution, Lemma 2 *)
  apply (tactic {* pair_tac "ex" 1 *})
  apply (simp add: executions_def)
  (* start state *)
  apply (rule conjI)
  apply (simp add: is_ref_map_def corresp_ex_def)
  (* is-execution-fragment *)
  apply (erule lemma_2 [THEN spec, THEN mp])
  apply (simp add: reachable.reachable_0)
  done


subsection "Corollary:  FAIR TRACE - INCLUSION"

lemma fininf: "(~inf_often P s) = fin_often P s"
apply (unfold fin_often_def)
apply auto
done


lemma WF_alt: "is_wfair A W (s,ex) =  
  (fin_often (%x. ~Enabled A W (snd x)) ex --> inf_often (%x. fst x :W) ex)"
apply (simp add: is_wfair_def fin_often_def)
apply auto
done

lemma WF_persistent: "[|is_wfair A W (s,ex); inf_often (%x. Enabled A W (snd x)) ex;  
          en_persistent A W|]  
    ==> inf_often (%x. fst x :W) ex"
apply (drule persistent)
apply assumption
apply (simp add: WF_alt)
apply auto
done


lemma fair_trace_inclusion: "!! C A.  
          [| is_ref_map f C A; ext C = ext A;  
          !! ex. [| ex:executions C; fair_ex C ex|] ==> fair_ex A (corresp_ex A f ex) |]  
          ==> fairtraces C <= fairtraces A"
apply (simp (no_asm) add: fairtraces_def fairexecutions_def)
apply (tactic "safe_tac set_cs")
apply (rule_tac x = "corresp_ex A f ex" in exI)
apply (tactic "safe_tac set_cs")

  (* Traces coincide, Lemma 1 *)
  apply (tactic {* pair_tac "ex" 1 *})
  apply (erule lemma_1 [THEN spec, THEN mp])
  apply assumption+
  apply (simp add: executions_def reachable.reachable_0)

  (* corresp_ex is execution, Lemma 2 *)
  apply (tactic {* pair_tac "ex" 1 *})
  apply (simp add: executions_def)
  (* start state *)
  apply (rule conjI)
  apply (simp add: is_ref_map_def corresp_ex_def)
  (* is-execution-fragment *)
  apply (erule lemma_2 [THEN spec, THEN mp])
  apply (simp add: reachable.reachable_0)

 (* Fairness *)
apply auto
done

lemma fair_trace_inclusion2: "!! C A.  
          [| inp(C) = inp(A); out(C)=out(A);  
             is_fair_ref_map f C A |]  
          ==> fair_implements C A"
apply (simp add: is_fair_ref_map_def fair_implements_def fairtraces_def fairexecutions_def)
apply (tactic "safe_tac set_cs")
apply (rule_tac x = "corresp_ex A f ex" in exI)
apply (tactic "safe_tac set_cs")
  (* Traces coincide, Lemma 1 *)
  apply (tactic {* pair_tac "ex" 1 *})
  apply (erule lemma_1 [THEN spec, THEN mp])
  apply (simp (no_asm) add: externals_def)
  apply (auto)[1]
  apply (simp add: executions_def reachable.reachable_0)

  (* corresp_ex is execution, Lemma 2 *)
  apply (tactic {* pair_tac "ex" 1 *})
  apply (simp add: executions_def)
  (* start state *)
  apply (rule conjI)
  apply (simp add: is_ref_map_def corresp_ex_def)
  (* is-execution-fragment *)
  apply (erule lemma_2 [THEN spec, THEN mp])
  apply (simp add: reachable.reachable_0)

 (* Fairness *)
apply auto
done


end
