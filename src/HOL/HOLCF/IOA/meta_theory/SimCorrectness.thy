(*  Title:      HOL/HOLCF/IOA/meta_theory/SimCorrectness.thy
    Author:     Olaf Müller
*)

header {* Correctness of Simulations in HOLCF/IOA *}

theory SimCorrectness
imports Simulations
begin

definition
  (* Note: s2 instead of s1 in last argument type !! *)
  corresp_ex_simC :: "('a,'s2)ioa => (('s1 * 's2)set) => ('a,'s1)pairs
                   -> ('s2 => ('a,'s2)pairs)" where
  "corresp_ex_simC A R = (fix$(LAM h ex. (%s. case ex of
      nil =>  nil
    | x##xs => (flift1 (%pr. let a = (fst pr); t = (snd pr);
                                 T' = @t'. ? ex1. (t,t'):R & move A ex1 s a t'
                             in
                                (@cex. move A cex s a T')
                                 @@ ((h$xs) T'))
                        $x) )))"

definition
  corresp_ex_sim :: "('a,'s2)ioa => (('s1 *'s2)set) =>
                      ('a,'s1)execution => ('a,'s2)execution" where
  "corresp_ex_sim A R ex == let S'= (@s'.(fst ex,s'):R & s': starts_of A)
                            in
                               (S',(corresp_ex_simC A R$(snd ex)) S')"


subsection "corresp_ex_sim"

lemma corresp_ex_simC_unfold: "corresp_ex_simC A R  = (LAM ex. (%s. case ex of
       nil =>  nil
     | x##xs => (flift1 (%pr. let a = (fst pr); t = (snd pr);
                                  T' = @t'. ? ex1. (t,t'):R & move A ex1 s a t'
                              in
                                 (@cex. move A cex s a T')
                               @@ ((corresp_ex_simC A R $xs) T'))
                         $x) ))"
apply (rule trans)
apply (rule fix_eq2)
apply (simp only: corresp_ex_simC_def)
apply (rule beta_cfun)
apply (simp add: flift1_def)
done

lemma corresp_ex_simC_UU: "(corresp_ex_simC A R$UU) s=UU"
apply (subst corresp_ex_simC_unfold)
apply simp
done

lemma corresp_ex_simC_nil: "(corresp_ex_simC A R$nil) s = nil"
apply (subst corresp_ex_simC_unfold)
apply simp
done

lemma corresp_ex_simC_cons: "(corresp_ex_simC A R$((a,t)>>xs)) s =
           (let T' = @t'. ? ex1. (t,t'):R & move A ex1 s a t'
            in
             (@cex. move A cex s a T')
              @@ ((corresp_ex_simC A R$xs) T'))"
apply (rule trans)
apply (subst corresp_ex_simC_unfold)
apply (simp add: Consq_def flift1_def)
apply simp
done


declare corresp_ex_simC_UU [simp] corresp_ex_simC_nil [simp] corresp_ex_simC_cons [simp]


subsection "properties of move"

declare Let_def [simp del]

lemma move_is_move_sim:
   "[|is_simulation R C A; reachable C s; s -a--C-> t; (s,s'):R|] ==>
      let T' = @t'. ? ex1. (t,t'):R & move A ex1 s' a t' in
      (t,T'): R & move A (@ex2. move A ex2 s' a T') s' a T'"
apply (unfold is_simulation_def)

(* Does not perform conditional rewriting on assumptions automatically as
   usual. Instantiate all variables per hand. Ask Tobias?? *)
apply (subgoal_tac "? t' ex. (t,t') :R & move A ex s' a t'")
prefer 2
apply simp
apply (erule conjE)
apply (erule_tac x = "s" in allE)
apply (erule_tac x = "s'" in allE)
apply (erule_tac x = "t" in allE)
apply (erule_tac x = "a" in allE)
apply simp
(* Go on as usual *)
apply (erule exE)
apply (drule_tac x = "t'" and P = "%t'. ? ex. (t,t') :R & move A ex s' a t'" in someI)
apply (erule exE)
apply (erule conjE)
apply (simp add: Let_def)
apply (rule_tac x = "ex" in someI)
apply (erule conjE)
apply assumption
done

declare Let_def [simp]

lemma move_subprop1_sim:
   "[|is_simulation R C A; reachable C s; s-a--C-> t; (s,s'):R|] ==>
    let T' = @t'. ? ex1. (t,t'):R & move A ex1 s' a t' in
     is_exec_frag A (s',@x. move A x s' a T')"
apply (cut_tac move_is_move_sim)
defer
apply assumption+
apply (simp add: move_def)
done

lemma move_subprop2_sim:
   "[|is_simulation R C A; reachable C s; s-a--C-> t; (s,s'):R|] ==>
    let T' = @t'. ? ex1. (t,t'):R & move A ex1 s' a t' in
    Finite (@x. move A x s' a T')"
apply (cut_tac move_is_move_sim)
defer
apply assumption+
apply (simp add: move_def)
done

lemma move_subprop3_sim:
   "[|is_simulation R C A; reachable C s; s-a--C-> t; (s,s'):R|] ==>
    let T' = @t'. ? ex1. (t,t'):R & move A ex1 s' a t' in
     laststate (s',@x. move A x s' a T') = T'"
apply (cut_tac move_is_move_sim)
defer
apply assumption+
apply (simp add: move_def)
done

lemma move_subprop4_sim:
   "[|is_simulation R C A; reachable C s; s-a--C-> t; (s,s'):R|] ==>
    let T' = @t'. ? ex1. (t,t'):R & move A ex1 s' a t' in
      mk_trace A$((@x. move A x s' a T')) =
        (if a:ext A then a>>nil else nil)"
apply (cut_tac move_is_move_sim)
defer
apply assumption+
apply (simp add: move_def)
done

lemma move_subprop5_sim:
   "[|is_simulation R C A; reachable C s; s-a--C-> t; (s,s'):R|] ==>
    let T' = @t'. ? ex1. (t,t'):R & move A ex1 s' a t' in
      (t,T'):R"
apply (cut_tac move_is_move_sim)
defer
apply assumption+
apply (simp add: move_def)
done


subsection {* TRACE INCLUSION Part 1: Traces coincide *}

subsubsection "Lemmata for <=="

(* ------------------------------------------------------
                 Lemma 1 :Traces coincide
   ------------------------------------------------------- *)

declare split_if [split del]
lemma traces_coincide_sim [rule_format (no_asm)]:
  "[|is_simulation R C A; ext C = ext A|] ==>
         !s s'. reachable C s & is_exec_frag C (s,ex) & (s,s'): R -->
             mk_trace C$ex = mk_trace A$((corresp_ex_simC A R$ex) s')"

apply (tactic {* pair_induct_tac @{context} "ex" [@{thm is_exec_frag_def}] 1 *})
(* cons case *)
apply auto
apply (rename_tac ex a t s s')
apply (simp add: mk_traceConc)
apply (frule reachable.reachable_n)
apply assumption
apply (erule_tac x = "t" in allE)
apply (erule_tac x = "@t'. ? ex1. (t,t') :R & move A ex1 s' a t'" in allE)
apply (simp add: move_subprop5_sim [unfolded Let_def]
  move_subprop4_sim [unfolded Let_def] split add: split_if)
done
declare split_if [split]


(* ----------------------------------------------------------- *)
(*               Lemma 2 : corresp_ex_sim is execution         *)
(* ----------------------------------------------------------- *)


lemma correspsim_is_execution [rule_format (no_asm)]:
 "[| is_simulation R C A |] ==>
  !s s'. reachable C s & is_exec_frag C (s,ex) & (s,s'):R
  --> is_exec_frag A (s',(corresp_ex_simC A R$ex) s')"

apply (tactic {* pair_induct_tac @{context} "ex" [@{thm is_exec_frag_def}] 1 *})
(* main case *)
apply auto
apply (rename_tac ex a t s s')
apply (rule_tac t = "@t'. ? ex1. (t,t') :R & move A ex1 s' a t'" in lemma_2_1)

(* Finite *)
apply (erule move_subprop2_sim [unfolded Let_def])
apply assumption+
apply (rule conjI)

(* is_exec_frag *)
apply (erule move_subprop1_sim [unfolded Let_def])
apply assumption+
apply (rule conjI)

(* Induction hypothesis  *)
(* reachable_n looping, therefore apply it manually *)
apply (erule_tac x = "t" in allE)
apply (erule_tac x = "@t'. ? ex1. (t,t') :R & move A ex1 s' a t'" in allE)
apply simp
apply (frule reachable.reachable_n)
apply assumption
apply (simp add: move_subprop5_sim [unfolded Let_def])
(* laststate *)
apply (erule move_subprop3_sim [unfolded Let_def, symmetric])
apply assumption+
done


subsection "Main Theorem: TRACE - INCLUSION"

(* -------------------------------------------------------------------------------- *)

  (* generate condition (s,S'):R & S':starts_of A, the first being intereting
     for the induction cases concerning the two lemmas correpsim_is_execution and
     traces_coincide_sim, the second for the start state case.
     S':= @s'. (s,s'):R & s':starts_of A, where s:starts_of C  *)

lemma simulation_starts:
"[| is_simulation R C A; s:starts_of C |]
  ==> let S' = @s'. (s,s'):R & s':starts_of A in
      (s,S'):R & S':starts_of A"
  apply (simp add: is_simulation_def corresp_ex_sim_def Int_non_empty Image_def)
  apply (erule conjE)+
  apply (erule ballE)
  prefer 2 apply (blast)
  apply (erule exE)
  apply (rule someI2)
  apply assumption
  apply blast
  done

lemmas sim_starts1 = simulation_starts [unfolded Let_def, THEN conjunct1]
lemmas sim_starts2 = simulation_starts [unfolded Let_def, THEN conjunct2]


lemma trace_inclusion_for_simulations:
  "[| ext C = ext A; is_simulation R C A |]
           ==> traces C <= traces A"

  apply (unfold traces_def)

  apply (simp (no_asm) add: has_trace_def2)
  apply auto

  (* give execution of abstract automata *)
  apply (rule_tac x = "corresp_ex_sim A R ex" in bexI)

  (* Traces coincide, Lemma 1 *)
  apply (tactic {* pair_tac @{context} "ex" 1 *})
  apply (rename_tac s ex)
  apply (simp (no_asm) add: corresp_ex_sim_def)
  apply (rule_tac s = "s" in traces_coincide_sim)
  apply assumption+
  apply (simp add: executions_def reachable.reachable_0 sim_starts1)

  (* corresp_ex_sim is execution, Lemma 2 *)
  apply (tactic {* pair_tac @{context} "ex" 1 *})
  apply (simp add: executions_def)
  apply (rename_tac s ex)

  (* start state *)
  apply (rule conjI)
  apply (simp add: sim_starts2 corresp_ex_sim_def)

  (* is-execution-fragment *)
  apply (simp add: corresp_ex_sim_def)
  apply (rule_tac s = s in correspsim_is_execution)
  apply assumption
  apply (simp add: reachable.reachable_0 sim_starts1)
  done

end
