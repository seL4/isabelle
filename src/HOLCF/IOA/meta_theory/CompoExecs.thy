(*  Title:      HOLCF/IOA/meta_theory/CompoExecs.thy
    ID:         $Id$
    Author:     Olaf Müller
*)

header {* Compositionality on Execution level *}

theory CompoExecs
imports Traces
begin

consts

 ProjA      ::"('a,'s * 't)execution => ('a,'s)execution"
 ProjA2     ::"('a,'s * 't)pairs     -> ('a,'s)pairs"
 ProjB      ::"('a,'s * 't)execution => ('a,'t)execution"
 ProjB2     ::"('a,'s * 't)pairs     -> ('a,'t)pairs"
 Filter_ex  ::"'a signature => ('a,'s)execution => ('a,'s)execution"
 Filter_ex2 ::"'a signature => ('a,'s)pairs     -> ('a,'s)pairs"
 stutter    ::"'a signature => ('a,'s)execution => bool"
 stutter2   ::"'a signature => ('a,'s)pairs     -> ('s => tr)"

 par_execs  ::"[('a,'s)execution_module,('a,'t)execution_module] => ('a,'s*'t)execution_module"


defs


ProjA_def:
 "ProjA ex == (fst (fst ex), ProjA2$(snd ex))"

ProjB_def:
 "ProjB ex == (snd (fst ex), ProjB2$(snd ex))"


ProjA2_def:
  "ProjA2 == Map (%x.(fst x,fst(snd x)))"

ProjB2_def:
  "ProjB2 == Map (%x.(fst x,snd(snd x)))"


Filter_ex_def:
  "Filter_ex sig ex == (fst ex,Filter_ex2 sig$(snd ex))"


Filter_ex2_def:
  "Filter_ex2 sig ==  Filter (%x. fst x:actions sig)"

stutter_def:
  "stutter sig ex == ((stutter2 sig$(snd ex)) (fst ex) ~= FF)"

stutter2_def:
  "stutter2 sig ==(fix$(LAM h ex. (%s. case ex of
      nil => TT
    | x##xs => (flift1
            (%p.(If Def ((fst p)~:actions sig)
                 then Def (s=(snd p))
                 else TT fi)
                andalso (h$xs) (snd p))
             $x)
   )))"

par_execs_def:
  "par_execs ExecsA ExecsB ==
       let exA = fst ExecsA; sigA = snd ExecsA;
           exB = fst ExecsB; sigB = snd ExecsB
       in
       (    {ex. Filter_ex sigA (ProjA ex) : exA}
        Int {ex. Filter_ex sigB (ProjB ex) : exB}
        Int {ex. stutter sigA (ProjA ex)}
        Int {ex. stutter sigB (ProjB ex)}
        Int {ex. Forall (%x. fst x:(actions sigA Un actions sigB)) (snd ex)},
        asig_comp sigA sigB)"



lemmas [simp del] = ex_simps all_simps split_paired_All


section "recursive equations of operators"


(* ---------------------------------------------------------------- *)
(*                               ProjA2                             *)
(* ---------------------------------------------------------------- *)


lemma ProjA2_UU: "ProjA2$UU = UU"
apply (simp add: ProjA2_def)
done

lemma ProjA2_nil: "ProjA2$nil = nil"
apply (simp add: ProjA2_def)
done

lemma ProjA2_cons: "ProjA2$((a,t)>>xs) = (a,fst t) >> ProjA2$xs"
apply (simp add: ProjA2_def)
done


(* ---------------------------------------------------------------- *)
(*                               ProjB2                             *)
(* ---------------------------------------------------------------- *)


lemma ProjB2_UU: "ProjB2$UU = UU"
apply (simp add: ProjB2_def)
done

lemma ProjB2_nil: "ProjB2$nil = nil"
apply (simp add: ProjB2_def)
done

lemma ProjB2_cons: "ProjB2$((a,t)>>xs) = (a,snd t) >> ProjB2$xs"
apply (simp add: ProjB2_def)
done



(* ---------------------------------------------------------------- *)
(*                             Filter_ex2                           *)
(* ---------------------------------------------------------------- *)


lemma Filter_ex2_UU: "Filter_ex2 sig$UU=UU"
apply (simp add: Filter_ex2_def)
done

lemma Filter_ex2_nil: "Filter_ex2 sig$nil=nil"
apply (simp add: Filter_ex2_def)
done

lemma Filter_ex2_cons: "Filter_ex2 sig$(at >> xs) =     
             (if (fst at:actions sig)     
                  then at >> (Filter_ex2 sig$xs)  
                  else        Filter_ex2 sig$xs)"

apply (simp add: Filter_ex2_def)
done


(* ---------------------------------------------------------------- *)
(*                             stutter2                             *)
(* ---------------------------------------------------------------- *)


lemma stutter2_unfold: "stutter2 sig = (LAM ex. (%s. case ex of  
       nil => TT  
     | x##xs => (flift1  
             (%p.(If Def ((fst p)~:actions sig)  
                  then Def (s=(snd p))  
                  else TT fi)  
                 andalso (stutter2 sig$xs) (snd p))   
              $x)  
            ))"
apply (rule trans)
apply (rule fix_eq2)
apply (rule stutter2_def)
apply (rule beta_cfun)
apply (simp add: flift1_def)
done

lemma stutter2_UU: "(stutter2 sig$UU) s=UU"
apply (subst stutter2_unfold)
apply simp
done

lemma stutter2_nil: "(stutter2 sig$nil) s = TT"
apply (subst stutter2_unfold)
apply simp
done

lemma stutter2_cons: "(stutter2 sig$(at>>xs)) s =  
               ((if (fst at)~:actions sig then Def (s=snd at) else TT)  
                 andalso (stutter2 sig$xs) (snd at))"
apply (rule trans)
apply (subst stutter2_unfold)
apply (simp add: Consq_def flift1_def If_and_if)
apply simp
done


declare stutter2_UU [simp] stutter2_nil [simp] stutter2_cons [simp]


(* ---------------------------------------------------------------- *)
(*                             stutter                              *)
(* ---------------------------------------------------------------- *)

lemma stutter_UU: "stutter sig (s, UU)"
apply (simp add: stutter_def)
done

lemma stutter_nil: "stutter sig (s, nil)"
apply (simp add: stutter_def)
done

lemma stutter_cons: "stutter sig (s, (a,t)>>ex) =  
      ((a~:actions sig --> (s=t)) & stutter sig (t,ex))"
apply (simp add: stutter_def)
done

(* ----------------------------------------------------------------------------------- *)

declare stutter2_UU [simp del] stutter2_nil [simp del] stutter2_cons [simp del]

lemmas compoex_simps = ProjA2_UU ProjA2_nil ProjA2_cons
  ProjB2_UU ProjB2_nil ProjB2_cons
  Filter_ex2_UU Filter_ex2_nil Filter_ex2_cons
  stutter_UU stutter_nil stutter_cons

declare compoex_simps [simp]



(* ------------------------------------------------------------------ *)
(*                      The following lemmata aim for                 *)
(*             COMPOSITIONALITY   on    EXECUTION     Level           *)
(* ------------------------------------------------------------------ *)


(* --------------------------------------------------------------------- *)
(*  Lemma_1_1a : is_ex_fr propagates from A||B to Projections A and B    *)
(* --------------------------------------------------------------------- *)

lemma lemma_1_1a: "!s. is_exec_frag (A||B) (s,xs)  
       -->  is_exec_frag A (fst s, Filter_ex2 (asig_of A)$(ProjA2$xs)) & 
            is_exec_frag B (snd s, Filter_ex2 (asig_of B)$(ProjB2$xs))"

apply (tactic {* pair_induct_tac "xs" [thm "is_exec_frag_def"] 1 *})
(* main case *)
apply (rename_tac ss a t)
apply (tactic "safe_tac set_cs")
apply (simp_all add: trans_of_defs2)
done


(* --------------------------------------------------------------------- *)
(*  Lemma_1_1b : is_ex_fr (A||B) implies stuttering on Projections       *)
(* --------------------------------------------------------------------- *)

lemma lemma_1_1b: "!s. is_exec_frag (A||B) (s,xs)  
       --> stutter (asig_of A) (fst s,ProjA2$xs)  & 
           stutter (asig_of B) (snd s,ProjB2$xs)"

apply (tactic {* pair_induct_tac "xs" [thm "stutter_def", thm "is_exec_frag_def"] 1 *})
(* main case *)
apply (tactic "safe_tac set_cs")
apply (simp_all add: trans_of_defs2)
done


(* --------------------------------------------------------------------- *)
(*  Lemma_1_1c : Executions of A||B have only  A- or B-actions           *)
(* --------------------------------------------------------------------- *)

lemma lemma_1_1c: "!s. (is_exec_frag (A||B) (s,xs)  
   --> Forall (%x. fst x:act (A||B)) xs)"

apply (tactic {* pair_induct_tac "xs" [thm "Forall_def", thm "sforall_def",
  thm "is_exec_frag_def"] 1 *})
(* main case *)
apply (tactic "safe_tac set_cs")
apply (simp_all add: trans_of_defs2 actions_asig_comp asig_of_par)
done


(* ----------------------------------------------------------------------- *)
(*  Lemma_1_2 : ex A, exB, stuttering and forall a:A|B implies ex (A||B)   *)
(* ----------------------------------------------------------------------- *)

lemma lemma_1_2: 
"!s. is_exec_frag A (fst s,Filter_ex2 (asig_of A)$(ProjA2$xs)) & 
     is_exec_frag B (snd s,Filter_ex2 (asig_of B)$(ProjB2$xs)) & 
     stutter (asig_of A) (fst s,(ProjA2$xs)) &  
     stutter (asig_of B) (snd s,(ProjB2$xs)) &  
     Forall (%x. fst x:act (A||B)) xs  
     --> is_exec_frag (A||B) (s,xs)"

apply (tactic {* pair_induct_tac "xs" [thm "Forall_def", thm "sforall_def",
  thm "is_exec_frag_def", thm "stutter_def"] 1 *})
apply (simp add: trans_of_defs1 actions_asig_comp asig_of_par)
apply (tactic "safe_tac set_cs")
apply simp
apply simp
done


subsection {* COMPOSITIONALITY on EXECUTION Level -- Main Theorem *}

lemma compositionality_ex: 
"(ex:executions(A||B)) = 
 (Filter_ex (asig_of A) (ProjA ex) : executions A & 
  Filter_ex (asig_of B) (ProjB ex) : executions B & 
  stutter (asig_of A) (ProjA ex) & stutter (asig_of B) (ProjB ex) & 
  Forall (%x. fst x:act (A||B)) (snd ex))"

apply (simp (no_asm) add: executions_def ProjB_def Filter_ex_def ProjA_def starts_of_par)
apply (tactic {* pair_tac "ex" 1 *})
apply (rule iffI)
(* ==>  *)
apply (erule conjE)+
apply (simp add: lemma_1_1a lemma_1_1b lemma_1_1c)
(* <==  *)
apply (erule conjE)+
apply (simp add: lemma_1_2)
done


subsection {* COMPOSITIONALITY on EXECUTION Level -- for Modules *}

lemma compositionality_ex_modules: 
  "Execs (A||B) = par_execs (Execs A) (Execs B)"
apply (unfold Execs_def par_execs_def)
apply (simp add: asig_of_par)
apply (rule set_ext)
apply (simp add: compositionality_ex actions_of_par)
done

end
