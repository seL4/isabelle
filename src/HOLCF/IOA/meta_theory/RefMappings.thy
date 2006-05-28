(*  Title:      HOLCF/IOA/meta_theory/RefMappings.thy
    ID:         $Id$
    Author:     Olaf Müller
*)

header {* Refinement Mappings in HOLCF/IOA *}

theory RefMappings
imports Traces
begin

defaultsort type

consts
  move         ::"[('a,'s)ioa,('a,'s)pairs,'s,'a,'s] => bool"
  is_ref_map   ::"[('s1=>'s2),('a,'s1)ioa,('a,'s2)ioa] => bool"
  is_weak_ref_map ::"[('s1=>'s2),('a,'s1)ioa,('a,'s2)ioa] => bool"


defs

move_def:
  "move ioa ex s a t ==
    (is_exec_frag ioa (s,ex) &  Finite ex &
     laststate (s,ex)=t  &
     mk_trace ioa$ex = (if a:ext(ioa) then a>>nil else nil))"

is_ref_map_def:
  "is_ref_map f C A ==
   (!s:starts_of(C). f(s):starts_of(A)) &
   (!s t a. reachable C s &
            s -a--C-> t
            --> (? ex. move A ex (f s) a (f t)))"

is_weak_ref_map_def:
  "is_weak_ref_map f C A ==
   (!s:starts_of(C). f(s):starts_of(A)) &
   (!s t a. reachable C s &
            s -a--C-> t
            --> (if a:ext(C)
                 then (f s) -a--A-> (f t)
                 else (f s)=(f t)))"


subsection "transitions and moves"


lemma transition_is_ex: "s -a--A-> t ==> ? ex. move A ex s a t"
apply (rule_tac x = " (a,t) >>nil" in exI)
apply (simp add: move_def)
done


lemma nothing_is_ex: "(~a:ext A) & s=t ==> ? ex. move A ex s a t"
apply (rule_tac x = "nil" in exI)
apply (simp add: move_def)
done


lemma ei_transitions_are_ex: "(s -a--A-> s') & (s' -a'--A-> s'') & (~a':ext A)  
         ==> ? ex. move A ex s a s''"
apply (rule_tac x = " (a,s') >> (a',s'') >>nil" in exI)
apply (simp add: move_def)
done


lemma eii_transitions_are_ex: "(s1 -a1--A-> s2) & (s2 -a2--A-> s3) & (s3 -a3--A-> s4) & 
      (~a2:ext A) & (~a3:ext A) ==>  
      ? ex. move A ex s1 a1 s4"
apply (rule_tac x = " (a1,s2) >> (a2,s3) >> (a3,s4) >>nil" in exI)
apply (simp add: move_def)
done


subsection "weak_ref_map and ref_map"

lemma imp_conj_lemma: 
  "[| ext C = ext A;  
     is_weak_ref_map f C A |] ==> is_ref_map f C A"
apply (unfold is_weak_ref_map_def is_ref_map_def)
apply (tactic "safe_tac set_cs")
apply (case_tac "a:ext A")
apply (rule transition_is_ex)
apply (simp (no_asm_simp))
apply (rule nothing_is_ex)
apply simp
done


lemma imp_conj_lemma: "(P ==> Q-->R) ==> P&Q --> R"
  by blast

declare split_if [split del]
declare if_weak_cong [cong del]

lemma rename_through_pmap: "[| is_weak_ref_map f C A |]  
      ==> (is_weak_ref_map f (rename C g) (rename A g))"
apply (simp add: is_weak_ref_map_def)
apply (rule conjI)
(* 1: start states *)
apply (simp add: rename_def rename_set_def starts_of_def)
(* 2: reachable transitions *)
apply (rule allI)+
apply (rule imp_conj_lemma)
apply (simp (no_asm) add: rename_def rename_set_def)
apply (simp add: externals_def asig_inputs_def asig_outputs_def asig_of_def trans_of_def)
apply safe
apply (simplesubst split_if)
 apply (rule conjI)
 apply (rule impI)
 apply (erule disjE)
 apply (erule exE)
apply (erule conjE)
(* x is input *)
 apply (drule sym)
 apply (drule sym)
apply simp
apply hypsubst+
apply (frule reachable_rename)
apply simp
(* x is output *)
 apply (erule exE)
apply (erule conjE)
 apply (drule sym)
 apply (drule sym)
apply simp
apply hypsubst+
apply (frule reachable_rename)
apply simp
(* x is internal *)
apply (frule reachable_rename)
apply auto
done

declare split_if [split]
declare if_weak_cong [cong]

end
