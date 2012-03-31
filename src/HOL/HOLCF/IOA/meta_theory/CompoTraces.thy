(*  Title:      HOL/HOLCF/IOA/meta_theory/CompoTraces.thy
    Author:     Olaf Müller
*) 

header {* Compositionality on Trace level *}

theory CompoTraces
imports CompoScheds ShortExecutions
begin
 

consts  

 mksch      ::"('a,'s)ioa => ('a,'t)ioa => 'a Seq -> 'a Seq -> 'a Seq -> 'a Seq" 
 par_traces ::"['a trace_module,'a trace_module] => 'a trace_module"

defs

mksch_def:
  "mksch A B == (fix$(LAM h tr schA schB. case tr of 
       nil => nil
    | x##xs => 
      (case x of 
        UU => UU
      | Def y => 
         (if y:act A then 
             (if y:act B then 
                   ((Takewhile (%a. a:int A)$schA)
                      @@ (Takewhile (%a. a:int B)$schB)
                           @@ (y>>(h$xs
                                    $(TL$(Dropwhile (%a. a:int A)$schA))
                                    $(TL$(Dropwhile (%a. a:int B)$schB))
                    )))
              else
                 ((Takewhile (%a. a:int A)$schA)
                  @@ (y>>(h$xs
                           $(TL$(Dropwhile (%a. a:int A)$schA))
                           $schB)))
              )
          else 
             (if y:act B then 
                 ((Takewhile (%a. a:int B)$schB)
                     @@ (y>>(h$xs
                              $schA
                              $(TL$(Dropwhile (%a. a:int B)$schB))
                              )))
             else
               UU
             )
         )
       )))"


par_traces_def:
  "par_traces TracesA TracesB == 
       let trA = fst TracesA; sigA = snd TracesA; 
           trB = fst TracesB; sigB = snd TracesB       
       in
       (    {tr. Filter (%a. a:actions sigA)$tr : trA}
        Int {tr. Filter (%a. a:actions sigB)$tr : trB}
        Int {tr. Forall (%x. x:(externals sigA Un externals sigB)) tr},
        asig_comp sigA sigB)"

axiomatization where

finiteR_mksch:
  "Finite (mksch A B$tr$x$y) --> Finite tr"


declaration {* fn _ => Simplifier.map_ss (Simplifier.set_mksym (K (K NONE))) *}


subsection "mksch rewrite rules"

lemma mksch_unfold:
"mksch A B = (LAM tr schA schB. case tr of 
       nil => nil
    | x##xs => 
      (case x of  
        UU => UU  
      | Def y => 
         (if y:act A then 
             (if y:act B then 
                   ((Takewhile (%a. a:int A)$schA) 
                         @@(Takewhile (%a. a:int B)$schB) 
                              @@(y>>(mksch A B$xs   
                                       $(TL$(Dropwhile (%a. a:int A)$schA))  
                                       $(TL$(Dropwhile (%a. a:int B)$schB))  
                    )))   
              else  
                 ((Takewhile (%a. a:int A)$schA)  
                      @@ (y>>(mksch A B$xs  
                              $(TL$(Dropwhile (%a. a:int A)$schA))  
                              $schB)))  
              )   
          else    
             (if y:act B then  
                 ((Takewhile (%a. a:int B)$schB)  
                       @@ (y>>(mksch A B$xs   
                              $schA   
                              $(TL$(Dropwhile (%a. a:int B)$schB))  
                              )))  
             else  
               UU  
             )  
         )  
       ))"
apply (rule trans)
apply (rule fix_eq2)
apply (rule mksch_def)
apply (rule beta_cfun)
apply simp
done

lemma mksch_UU: "mksch A B$UU$schA$schB = UU"
apply (subst mksch_unfold)
apply simp
done

lemma mksch_nil: "mksch A B$nil$schA$schB = nil"
apply (subst mksch_unfold)
apply simp
done

lemma mksch_cons1: "[|x:act A;x~:act B|]   
    ==> mksch A B$(x>>tr)$schA$schB =  
          (Takewhile (%a. a:int A)$schA)  
          @@ (x>>(mksch A B$tr$(TL$(Dropwhile (%a. a:int A)$schA))  
                              $schB))"
apply (rule trans)
apply (subst mksch_unfold)
apply (simp add: Consq_def If_and_if)
apply (simp add: Consq_def)
done

lemma mksch_cons2: "[|x~:act A;x:act B|]  
    ==> mksch A B$(x>>tr)$schA$schB =  
         (Takewhile (%a. a:int B)$schB)   
          @@ (x>>(mksch A B$tr$schA$(TL$(Dropwhile (%a. a:int B)$schB))   
                             ))"
apply (rule trans)
apply (subst mksch_unfold)
apply (simp add: Consq_def If_and_if)
apply (simp add: Consq_def)
done

lemma mksch_cons3: "[|x:act A;x:act B|]  
    ==> mksch A B$(x>>tr)$schA$schB =  
             (Takewhile (%a. a:int A)$schA)  
          @@ ((Takewhile (%a. a:int B)$schB)   
          @@ (x>>(mksch A B$tr$(TL$(Dropwhile (%a. a:int A)$schA))  
                             $(TL$(Dropwhile (%a. a:int B)$schB))))   
              )"
apply (rule trans)
apply (subst mksch_unfold)
apply (simp add: Consq_def If_and_if)
apply (simp add: Consq_def)
done

lemmas compotr_simps = mksch_UU mksch_nil mksch_cons1 mksch_cons2 mksch_cons3

declare compotr_simps [simp]


subsection {* COMPOSITIONALITY on TRACE Level *}

subsubsection "Lemmata for ==>"

(* Consequence out of ext1_ext2_is_not_act1(2), which in turn are consequences out of
   the compatibility of IOA, in particular out of the condition that internals are
   really hidden. *)

lemma compatibility_consequence1: "(eB & ~eA --> ~A) -->        
          (A & (eA | eB)) = (eA & A)"
apply fast
done


(* very similar to above, only the commutativity of | is used to make a slight change *)

lemma compatibility_consequence2: "(eB & ~eA --> ~A) -->        
          (A & (eB | eA)) = (eA & A)"
apply fast
done


subsubsection "Lemmata for <=="

(* Lemma for substitution of looping assumption in another specific assumption *)
lemma subst_lemma1: "[| f << (g x) ; x=(h x) |] ==> f << g (h x)"
by (erule subst)

(* Lemma for substitution of looping assumption in another specific assumption *)
lemma subst_lemma2: "[| (f x) = y >> g; x=(h x) |] ==> (f (h x)) = y >> g"
by (erule subst)

lemma ForallAorB_mksch [rule_format]:
  "!!A B. compatible A B ==>  
    ! schA schB. Forall (%x. x:act (A||B)) tr  
    --> Forall (%x. x:act (A||B)) (mksch A B$tr$schA$schB)"
apply (tactic {* Seq_induct_tac @{context} "tr"
  [@{thm Forall_def}, @{thm sforall_def}, @{thm mksch_def}] 1 *})
apply auto
apply (simp add: actions_of_par)
apply (case_tac "a:act A")
apply (case_tac "a:act B")
(* a:A, a:B *)
apply simp
apply (rule Forall_Conc_impl [THEN mp])
apply (simp add: intA_is_not_actB int_is_act)
apply (rule Forall_Conc_impl [THEN mp])
apply (simp add: intA_is_not_actB int_is_act)
(* a:A,a~:B *)
apply simp
apply (rule Forall_Conc_impl [THEN mp])
apply (simp add: intA_is_not_actB int_is_act)
apply (case_tac "a:act B")
(* a~:A, a:B *)
apply simp
apply (rule Forall_Conc_impl [THEN mp])
apply (simp add: intA_is_not_actB int_is_act)
(* a~:A,a~:B *)
apply auto
done

lemma ForallBnAmksch [rule_format (no_asm)]: "!!A B. compatible B A  ==>  
    ! schA schB.  (Forall (%x. x:act B & x~:act A) tr  
    --> Forall (%x. x:act B & x~:act A) (mksch A B$tr$schA$schB))"
apply (tactic {* Seq_induct_tac @{context} "tr"
  [@{thm Forall_def}, @{thm sforall_def}, @{thm mksch_def}] 1 *})
apply auto
apply (rule Forall_Conc_impl [THEN mp])
apply (simp add: intA_is_not_actB int_is_act)
done

lemma ForallAnBmksch [rule_format (no_asm)]: "!!A B. compatible A B ==>  
    ! schA schB.  (Forall (%x. x:act A & x~:act B) tr  
    --> Forall (%x. x:act A & x~:act B) (mksch A B$tr$schA$schB))"
apply (tactic {* Seq_induct_tac @{context} "tr"
  [@{thm Forall_def}, @{thm sforall_def}, @{thm mksch_def}] 1 *})
apply auto
apply (rule Forall_Conc_impl [THEN mp])
apply (simp add: intA_is_not_actB int_is_act)
done

(* safe-tac makes too many case distinctions with this lemma in the next proof *)
declare FiniteConc [simp del]

lemma FiniteL_mksch [rule_format (no_asm)]: "[| Finite tr; is_asig(asig_of A); is_asig(asig_of B) |] ==>  
    ! x y. Forall (%x. x:act A) x & Forall (%x. x:act B) y &  
           Filter (%a. a:ext A)$x = Filter (%a. a:act A)$tr &  
           Filter (%a. a:ext B)$y = Filter (%a. a:act B)$tr & 
           Forall (%x. x:ext (A||B)) tr  
           --> Finite (mksch A B$tr$x$y)"

apply (erule Seq_Finite_ind)
apply simp
(* main case *)
apply simp
apply auto

(* a: act A; a: act B *)
apply (frule sym [THEN eq_imp_below, THEN divide_Seq])
apply (frule sym [THEN eq_imp_below, THEN divide_Seq])
back
apply (erule conjE)+
(* Finite (tw iA x) and Finite (tw iB y) *)
apply (simp add: not_ext_is_int_or_not_act FiniteConc)
(* now for conclusion IH applicable, but assumptions have to be transformed *)
apply (drule_tac x = "x" and g = "Filter (%a. a:act A) $s" in subst_lemma2)
apply assumption
apply (drule_tac x = "y" and g = "Filter (%a. a:act B) $s" in subst_lemma2)
apply assumption
(* IH *)
apply (simp add: not_ext_is_int_or_not_act ForallTL ForallDropwhile)

(* a: act B; a~: act A *)
apply (frule sym [THEN eq_imp_below, THEN divide_Seq])

apply (erule conjE)+
(* Finite (tw iB y) *)
apply (simp add: not_ext_is_int_or_not_act FiniteConc)
(* now for conclusion IH applicable, but assumptions have to be transformed *)
apply (drule_tac x = "y" and g = "Filter (%a. a:act B) $s" in subst_lemma2)
apply assumption
(* IH *)
apply (simp add: not_ext_is_int_or_not_act ForallTL ForallDropwhile)

(* a~: act B; a: act A *)
apply (frule sym [THEN eq_imp_below, THEN divide_Seq])

apply (erule conjE)+
(* Finite (tw iA x) *)
apply (simp add: not_ext_is_int_or_not_act FiniteConc)
(* now for conclusion IH applicable, but assumptions have to be transformed *)
apply (drule_tac x = "x" and g = "Filter (%a. a:act A) $s" in subst_lemma2)
apply assumption
(* IH *)
apply (simp add: not_ext_is_int_or_not_act ForallTL ForallDropwhile)

(* a~: act B; a~: act A *)
apply (fastforce intro!: ext_is_act simp: externals_of_par)
done

declare FiniteConc [simp]

declare FilterConc [simp del]

lemma reduceA_mksch1 [rule_format (no_asm)]: " [| Finite bs; is_asig(asig_of A); is_asig(asig_of B);compatible A B|] ==>   
 ! y. Forall (%x. x:act B) y & Forall (%x. x:act B & x~:act A) bs & 
     Filter (%a. a:ext B)$y = Filter (%a. a:act B)$(bs @@ z)  
     --> (? y1 y2.  (mksch A B$(bs @@ z)$x$y) = (y1 @@ (mksch A B$z$x$y2)) &  
                    Forall (%x. x:act B & x~:act A) y1 &  
                    Finite y1 & y = (y1 @@ y2) &  
                    Filter (%a. a:ext B)$y1 = bs)"
apply (frule_tac A1 = "A" in compat_commute [THEN iffD1])
apply (erule Seq_Finite_ind)
apply (rule allI)+
apply (rule impI)
apply (rule_tac x = "nil" in exI)
apply (rule_tac x = "y" in exI)
apply simp
(* main case *)
apply (rule allI)+
apply (rule impI)
apply simp
apply (erule conjE)+
apply simp
(* divide_Seq on s *)
apply (frule sym [THEN eq_imp_below, THEN divide_Seq])
apply (erule conjE)+
(* transform assumption f eB y = f B (s@z) *)
apply (drule_tac x = "y" and g = "Filter (%a. a:act B) $ (s@@z) " in subst_lemma2)
apply assumption
apply (simp add: not_ext_is_int_or_not_act FilterConc)
(* apply IH *)
apply (erule_tac x = "TL$ (Dropwhile (%a. a:int B) $y) " in allE)
apply (simp add: ForallTL ForallDropwhile FilterConc)
apply (erule exE)+
apply (erule conjE)+
apply (simp add: FilterConc)
(* for replacing IH in conclusion *)
apply (rotate_tac -2)
(* instantiate y1a and y2a *)
apply (rule_tac x = "Takewhile (%a. a:int B) $y @@ a>>y1" in exI)
apply (rule_tac x = "y2" in exI)
(* elminate all obligations up to two depending on Conc_assoc *)
apply (simp add: intA_is_not_actB int_is_act int_is_not_ext FilterConc)
apply (simp (no_asm) add: Conc_assoc FilterConc)
done

lemmas reduceA_mksch = conjI [THEN [6] conjI [THEN [5] reduceA_mksch1]]

lemma reduceB_mksch1 [rule_format]:
" [| Finite a_s; is_asig(asig_of A); is_asig(asig_of B);compatible A B|] ==>   
 ! x. Forall (%x. x:act A) x & Forall (%x. x:act A & x~:act B) a_s & 
     Filter (%a. a:ext A)$x = Filter (%a. a:act A)$(a_s @@ z)  
     --> (? x1 x2.  (mksch A B$(a_s @@ z)$x$y) = (x1 @@ (mksch A B$z$x2$y)) &  
                    Forall (%x. x:act A & x~:act B) x1 &  
                    Finite x1 & x = (x1 @@ x2) &  
                    Filter (%a. a:ext A)$x1 = a_s)"
apply (frule_tac A1 = "A" in compat_commute [THEN iffD1])
apply (erule Seq_Finite_ind)
apply (rule allI)+
apply (rule impI)
apply (rule_tac x = "nil" in exI)
apply (rule_tac x = "x" in exI)
apply simp
(* main case *)
apply (rule allI)+
apply (rule impI)
apply simp
apply (erule conjE)+
apply simp
(* divide_Seq on s *)
apply (frule sym [THEN eq_imp_below, THEN divide_Seq])
apply (erule conjE)+
(* transform assumption f eA x = f A (s@z) *)
apply (drule_tac x = "x" and g = "Filter (%a. a:act A) $ (s@@z) " in subst_lemma2)
apply assumption
apply (simp add: not_ext_is_int_or_not_act FilterConc)
(* apply IH *)
apply (erule_tac x = "TL$ (Dropwhile (%a. a:int A) $x) " in allE)
apply (simp add: ForallTL ForallDropwhile FilterConc)
apply (erule exE)+
apply (erule conjE)+
apply (simp add: FilterConc)
(* for replacing IH in conclusion *)
apply (rotate_tac -2)
(* instantiate y1a and y2a *)
apply (rule_tac x = "Takewhile (%a. a:int A) $x @@ a>>x1" in exI)
apply (rule_tac x = "x2" in exI)
(* elminate all obligations up to two depending on Conc_assoc *)
apply (simp add: intA_is_not_actB int_is_act int_is_not_ext FilterConc)
apply (simp (no_asm) add: Conc_assoc FilterConc)
done

lemmas reduceB_mksch = conjI [THEN [6] conjI [THEN [5] reduceB_mksch1]]

declare FilterConc [simp]


subsection "Filtering external actions out of mksch(tr,schA,schB) yields the oracle tr"

lemma FilterA_mksch_is_tr: 
"!! A B. [| compatible A B; compatible B A; 
            is_asig(asig_of A); is_asig(asig_of B) |] ==>  
  ! schA schB. Forall (%x. x:act A) schA & Forall (%x. x:act B) schB &  
  Forall (%x. x:ext (A||B)) tr &  
  Filter (%a. a:act A)$tr << Filter (%a. a:ext A)$schA & 
  Filter (%a. a:act B)$tr << Filter (%a. a:ext B)$schB   
  --> Filter (%a. a:ext (A||B))$(mksch A B$tr$schA$schB) = tr"

apply (tactic {* Seq_induct_tac @{context} "tr"
  [@{thm Forall_def}, @{thm sforall_def}, @{thm mksch_def}] 1 *})
(* main case *)
(* splitting into 4 cases according to a:A, a:B *)
apply auto

(* Case a:A, a:B *)
apply (frule divide_Seq)
apply (frule divide_Seq)
back
apply (erule conjE)+
(* filtering internals of A in schA and of B in schB is nil *)
apply (simp add: not_ext_is_int_or_not_act externals_of_par intA_is_not_extB int_is_not_ext)
(* conclusion of IH ok, but assumptions of IH have to be transformed *)
apply (drule_tac x = "schA" in subst_lemma1)
apply assumption
apply (drule_tac x = "schB" in subst_lemma1)
apply assumption
(* IH *)
apply (simp add: not_ext_is_int_or_not_act ForallTL ForallDropwhile)

(* Case a:A, a~:B *)
apply (frule divide_Seq)
apply (erule conjE)+
(* filtering internals of A is nil *)
apply (simp add: not_ext_is_int_or_not_act externals_of_par intA_is_not_extB int_is_not_ext)
apply (drule_tac x = "schA" in subst_lemma1)
apply assumption
apply (simp add: not_ext_is_int_or_not_act ForallTL ForallDropwhile)

(* Case a:B, a~:A *)
apply (frule divide_Seq)
apply (erule conjE)+
(* filtering internals of A is nil *)
apply (simp add: not_ext_is_int_or_not_act externals_of_par intA_is_not_extB int_is_not_ext)
apply (drule_tac x = "schB" in subst_lemma1)
back
apply assumption
apply (simp add: not_ext_is_int_or_not_act ForallTL ForallDropwhile)

(* Case a~:A, a~:B *)
apply (fastforce intro!: ext_is_act simp: externals_of_par)
done


subsection" Filter of mksch(tr,schA,schB) to A is schA -- take lemma proof"

lemma FilterAmksch_is_schA: "!! A B. [| compatible A B; compatible B A;  
  is_asig(asig_of A); is_asig(asig_of B) |] ==>  
  Forall (%x. x:ext (A||B)) tr &  
  Forall (%x. x:act A) schA & Forall (%x. x:act B) schB &  
  Filter (%a. a:ext A)$schA = Filter (%a. a:act A)$tr & 
  Filter (%a. a:ext B)$schB = Filter (%a. a:act B)$tr & 
  LastActExtsch A schA & LastActExtsch B schB   
  --> Filter (%a. a:act A)$(mksch A B$tr$schA$schB) = schA"
apply (intro strip)
apply (rule seq.take_lemma)
apply (rule mp)
prefer 2 apply assumption
back back back back
apply (rule_tac x = "schA" in spec)
apply (rule_tac x = "schB" in spec)
apply (rule_tac x = "tr" in spec)
apply (tactic "thin_tac' 5 1")
apply (rule nat_less_induct)
apply (rule allI)+
apply (rename_tac tr schB schA)
apply (intro strip)
apply (erule conjE)+

apply (case_tac "Forall (%x. x:act B & x~:act A) tr")

apply (rule seq_take_lemma [THEN iffD2, THEN spec])
apply (tactic "thin_tac' 5 1")


apply (case_tac "Finite tr")

(* both sides of this equation are nil *)
apply (subgoal_tac "schA=nil")
apply (simp (no_asm_simp))
(* first side: mksch = nil *)
apply (auto intro!: ForallQFilterPnil ForallBnAmksch FiniteL_mksch)[1]
(* second side: schA = nil *)
apply (erule_tac A = "A" in LastActExtimplnil)
apply (simp (no_asm_simp))
apply (erule_tac Q = "%x. x:act B & x~:act A" in ForallQFilterPnil)
apply assumption
apply fast

(* case ~ Finite s *)

(* both sides of this equation are UU *)
apply (subgoal_tac "schA=UU")
apply (simp (no_asm_simp))
(* first side: mksch = UU *)
apply (auto intro!: ForallQFilterPUU finiteR_mksch [THEN mp, COMP rev_contrapos] ForallBnAmksch)[1]
(* schA = UU *)
apply (erule_tac A = "A" in LastActExtimplUU)
apply (simp (no_asm_simp))
apply (erule_tac Q = "%x. x:act B & x~:act A" in ForallQFilterPUU)
apply assumption
apply fast

(* case" ~ Forall (%x.x:act B & x~:act A) s" *)

apply (drule divide_Seq3)

apply (erule exE)+
apply (erule conjE)+
apply hypsubst

(* bring in lemma reduceA_mksch *)
apply (frule_tac x = "schA" and y = "schB" and A = "A" and B = "B" in reduceA_mksch)
apply assumption+
apply (erule exE)+
apply (erule conjE)+

(* use reduceA_mksch to rewrite conclusion *)
apply hypsubst
apply simp

(* eliminate the B-only prefix *)

apply (subgoal_tac " (Filter (%a. a :act A) $y1) = nil")
apply (erule_tac [2] ForallQFilterPnil)
prefer 2 apply assumption
prefer 2 apply fast

(* Now real recursive step follows (in y) *)

apply simp
apply (case_tac "x:act A")
apply (case_tac "x~:act B")
apply (rotate_tac -2)
apply simp

apply (subgoal_tac "Filter (%a. a:act A & a:ext B) $y1=nil")
apply (rotate_tac -1)
apply simp
(* eliminate introduced subgoal 2 *)
apply (erule_tac [2] ForallQFilterPnil)
prefer 2 apply assumption
prefer 2 apply fast

(* bring in divide Seq for s *)
apply (frule sym [THEN eq_imp_below, THEN divide_Seq])
apply (erule conjE)+

(* subst divide_Seq in conclusion, but only at the righest occurence *)
apply (rule_tac t = "schA" in ssubst)
back
back
back
apply assumption

(* reduce trace_takes from n to strictly smaller k *)
apply (rule take_reduction)

(* f A (tw iA) = tw ~eA *)
apply (simp add: int_is_act not_ext_is_int_or_not_act)
apply (rule refl)
apply (simp add: int_is_act not_ext_is_int_or_not_act)
apply (rotate_tac -11)

(* now conclusion fulfills induction hypothesis, but assumptions are not ready *)

(* assumption Forall tr *)
(* assumption schB *)
apply (simp add: ext_and_act)
(* assumption schA *)
apply (drule_tac x = "schA" and g = "Filter (%a. a:act A) $rs" in subst_lemma2)
apply assumption
apply (simp add: int_is_not_ext)
(* assumptions concerning LastActExtsch, cannot be rewritten, as LastActExtsmalli are looping  *)
apply (drule_tac sch = "schA" and P = "%a. a:int A" in LastActExtsmall1)
apply (frule_tac ?sch1.0 = "y1" in LastActExtsmall2)
apply assumption

(* assumption Forall schA *)
apply (drule_tac s = "schA" and P = "Forall (%x. x:act A) " in subst)
apply assumption
apply (simp add: int_is_act)

(* case x:actions(asig_of A) & x: actions(asig_of B) *)


apply (rotate_tac -2)
apply simp

apply (subgoal_tac "Filter (%a. a:act A & a:ext B) $y1=nil")
apply (rotate_tac -1)
apply simp
(* eliminate introduced subgoal 2 *)
apply (erule_tac [2] ForallQFilterPnil)
prefer 2 apply (assumption)
prefer 2 apply (fast)

(* bring in divide Seq for s *)
apply (frule sym [THEN eq_imp_below, THEN divide_Seq])
apply (erule conjE)+

(* subst divide_Seq in conclusion, but only at the righest occurence *)
apply (rule_tac t = "schA" in ssubst)
back
back
back
apply assumption

(* f A (tw iA) = tw ~eA *)
apply (simp add: int_is_act not_ext_is_int_or_not_act)

(* rewrite assumption forall and schB *)
apply (rotate_tac 13)
apply (simp add: ext_and_act)

(* divide_Seq for schB2 *)
apply (frule_tac y = "y2" in sym [THEN eq_imp_below, THEN divide_Seq])
apply (erule conjE)+
(* assumption schA *)
apply (drule_tac x = "schA" and g = "Filter (%a. a:act A) $rs" in subst_lemma2)
apply assumption
apply (simp add: int_is_not_ext)

(* f A (tw iB schB2) = nil *)
apply (simp add: int_is_not_ext not_ext_is_int_or_not_act intA_is_not_actB)


(* reduce trace_takes from n to strictly smaller k *)
apply (rule take_reduction)
apply (rule refl)
apply (rule refl)

(* now conclusion fulfills induction hypothesis, but assumptions are not all ready *)

(* assumption schB *)
apply (drule_tac x = "y2" and g = "Filter (%a. a:act B) $rs" in subst_lemma2)
apply assumption
apply (simp add: intA_is_not_actB int_is_not_ext)

(* conclusions concerning LastActExtsch, cannot be rewritten, as LastActExtsmalli are looping  *)
apply (drule_tac sch = "schA" and P = "%a. a:int A" in LastActExtsmall1)
apply (frule_tac ?sch1.0 = "y1" in LastActExtsmall2)
apply assumption
apply (drule_tac sch = "y2" and P = "%a. a:int B" in LastActExtsmall1)

(* assumption Forall schA, and Forall schA are performed by ForallTL,ForallDropwhile *)
apply (simp add: ForallTL ForallDropwhile)

(* case x~:A & x:B  *)
(* cannot occur, as just this case has been scheduled out before as the B-only prefix *)
apply (case_tac "x:act B")
apply fast

(* case x~:A & x~:B  *)
(* cannot occur because of assumption: Forall (a:ext A | a:ext B) *)
apply (rotate_tac -9)
(* reduce forall assumption from tr to (x>>rs) *)
apply (simp add: externals_of_par)
apply (fast intro!: ext_is_act)

done



subsection" Filter of mksch(tr,schA,schB) to B is schB -- take lemma proof"

lemma FilterBmksch_is_schB: "!! A B. [| compatible A B; compatible B A;  
  is_asig(asig_of A); is_asig(asig_of B) |] ==>  
  Forall (%x. x:ext (A||B)) tr &  
  Forall (%x. x:act A) schA & Forall (%x. x:act B) schB &  
  Filter (%a. a:ext A)$schA = Filter (%a. a:act A)$tr & 
  Filter (%a. a:ext B)$schB = Filter (%a. a:act B)$tr & 
  LastActExtsch A schA & LastActExtsch B schB   
  --> Filter (%a. a:act B)$(mksch A B$tr$schA$schB) = schB"
apply (intro strip)
apply (rule seq.take_lemma)
apply (rule mp)
prefer 2 apply assumption
back back back back
apply (rule_tac x = "schA" in spec)
apply (rule_tac x = "schB" in spec)
apply (rule_tac x = "tr" in spec)
apply (tactic "thin_tac' 5 1")
apply (rule nat_less_induct)
apply (rule allI)+
apply (rename_tac tr schB schA)
apply (intro strip)
apply (erule conjE)+

apply (case_tac "Forall (%x. x:act A & x~:act B) tr")

apply (rule seq_take_lemma [THEN iffD2, THEN spec])
apply (tactic "thin_tac' 5 1")

apply (case_tac "Finite tr")

(* both sides of this equation are nil *)
apply (subgoal_tac "schB=nil")
apply (simp (no_asm_simp))
(* first side: mksch = nil *)
apply (auto intro!: ForallQFilterPnil ForallAnBmksch FiniteL_mksch)[1]
(* second side: schA = nil *)
apply (erule_tac A = "B" in LastActExtimplnil)
apply (simp (no_asm_simp))
apply (erule_tac Q = "%x. x:act A & x~:act B" in ForallQFilterPnil)
apply assumption
apply fast

(* case ~ Finite tr *)

(* both sides of this equation are UU *)
apply (subgoal_tac "schB=UU")
apply (simp (no_asm_simp))
(* first side: mksch = UU *)
apply (force intro!: ForallQFilterPUU finiteR_mksch [THEN mp, COMP rev_contrapos] ForallAnBmksch)
(* schA = UU *)
apply (erule_tac A = "B" in LastActExtimplUU)
apply (simp (no_asm_simp))
apply (erule_tac Q = "%x. x:act A & x~:act B" in ForallQFilterPUU)
apply assumption
apply fast

(* case" ~ Forall (%x.x:act B & x~:act A) s" *)

apply (drule divide_Seq3)

apply (erule exE)+
apply (erule conjE)+
apply hypsubst

(* bring in lemma reduceB_mksch *)
apply (frule_tac y = "schB" and x = "schA" and A = "A" and B = "B" in reduceB_mksch)
apply assumption+
apply (erule exE)+
apply (erule conjE)+

(* use reduceB_mksch to rewrite conclusion *)
apply hypsubst
apply simp

(* eliminate the A-only prefix *)

apply (subgoal_tac "(Filter (%a. a :act B) $x1) = nil")
apply (erule_tac [2] ForallQFilterPnil)
prefer 2 apply (assumption)
prefer 2 apply (fast)

(* Now real recursive step follows (in x) *)

apply simp
apply (case_tac "x:act B")
apply (case_tac "x~:act A")
apply (rotate_tac -2)
apply simp

apply (subgoal_tac "Filter (%a. a:act B & a:ext A) $x1=nil")
apply (rotate_tac -1)
apply simp
(* eliminate introduced subgoal 2 *)
apply (erule_tac [2] ForallQFilterPnil)
prefer 2 apply (assumption)
prefer 2 apply (fast)

(* bring in divide Seq for s *)
apply (frule sym [THEN eq_imp_below, THEN divide_Seq])
apply (erule conjE)+

(* subst divide_Seq in conclusion, but only at the righest occurence *)
apply (rule_tac t = "schB" in ssubst)
back
back
back
apply assumption

(* reduce trace_takes from n to strictly smaller k *)
apply (rule take_reduction)

(* f B (tw iB) = tw ~eB *)
apply (simp add: int_is_act not_ext_is_int_or_not_act)
apply (rule refl)
apply (simp add: int_is_act not_ext_is_int_or_not_act)
apply (rotate_tac -11)

(* now conclusion fulfills induction hypothesis, but assumptions are not ready *)

(* assumption schA *)
apply (simp add: ext_and_act)
(* assumption schB *)
apply (drule_tac x = "schB" and g = "Filter (%a. a:act B) $rs" in subst_lemma2)
apply assumption
apply (simp add: int_is_not_ext)
(* assumptions concerning LastActExtsch, cannot be rewritten, as LastActExtsmalli are looping  *)
apply (drule_tac sch = "schB" and P = "%a. a:int B" in LastActExtsmall1)
apply (frule_tac ?sch1.0 = "x1" in LastActExtsmall2)
apply assumption

(* assumption Forall schB *)
apply (drule_tac s = "schB" and P = "Forall (%x. x:act B) " in subst)
apply assumption
apply (simp add: int_is_act)

(* case x:actions(asig_of A) & x: actions(asig_of B) *)

apply (rotate_tac -2)
apply simp

apply (subgoal_tac "Filter (%a. a:act B & a:ext A) $x1=nil")
apply (rotate_tac -1)
apply simp
(* eliminate introduced subgoal 2 *)
apply (erule_tac [2] ForallQFilterPnil)
prefer 2 apply (assumption)
prefer 2 apply (fast)

(* bring in divide Seq for s *)
apply (frule sym [THEN eq_imp_below, THEN divide_Seq])
apply (erule conjE)+

(* subst divide_Seq in conclusion, but only at the righest occurence *)
apply (rule_tac t = "schB" in ssubst)
back
back
back
apply assumption

(* f B (tw iB) = tw ~eB *)
apply (simp add: int_is_act not_ext_is_int_or_not_act)

(* rewrite assumption forall and schB *)
apply (rotate_tac 13)
apply (simp add: ext_and_act)

(* divide_Seq for schB2 *)
apply (frule_tac y = "x2" in sym [THEN eq_imp_below, THEN divide_Seq])
apply (erule conjE)+
(* assumption schA *)
apply (drule_tac x = "schB" and g = "Filter (%a. a:act B) $rs" in subst_lemma2)
apply assumption
apply (simp add: int_is_not_ext)

(* f B (tw iA schA2) = nil *)
apply (simp add: int_is_not_ext not_ext_is_int_or_not_act intA_is_not_actB)


(* reduce trace_takes from n to strictly smaller k *)
apply (rule take_reduction)
apply (rule refl)
apply (rule refl)

(* now conclusion fulfills induction hypothesis, but assumptions are not all ready *)

(* assumption schA *)
apply (drule_tac x = "x2" and g = "Filter (%a. a:act A) $rs" in subst_lemma2)
apply assumption
apply (simp add: intA_is_not_actB int_is_not_ext)

(* conclusions concerning LastActExtsch, cannot be rewritten, as LastActExtsmalli are looping  *)
apply (drule_tac sch = "schB" and P = "%a. a:int B" in LastActExtsmall1)
apply (frule_tac ?sch1.0 = "x1" in LastActExtsmall2)
apply assumption
apply (drule_tac sch = "x2" and P = "%a. a:int A" in LastActExtsmall1)

(* assumption Forall schA, and Forall schA are performed by ForallTL,ForallDropwhile *)
apply (simp add: ForallTL ForallDropwhile)

(* case x~:B & x:A  *)
(* cannot occur, as just this case has been scheduled out before as the B-only prefix *)
apply (case_tac "x:act A")
apply fast

(* case x~:B & x~:A  *)
(* cannot occur because of assumption: Forall (a:ext A | a:ext B) *)
apply (rotate_tac -9)
(* reduce forall assumption from tr to (x>>rs) *)
apply (simp add: externals_of_par)
apply (fast intro!: ext_is_act)

done


subsection "COMPOSITIONALITY on TRACE Level -- Main Theorem"

lemma compositionality_tr: 
"!! A B. [| is_trans_of A; is_trans_of B; compatible A B; compatible B A;  
            is_asig(asig_of A); is_asig(asig_of B)|]  
        ==>  (tr: traces(A||B)) =  
             (Filter (%a. a:act A)$tr : traces A & 
              Filter (%a. a:act B)$tr : traces B & 
              Forall (%x. x:ext(A||B)) tr)"

apply (simp (no_asm) add: traces_def has_trace_def)
apply auto

(* ==> *)
(* There is a schedule of A *)
apply (rule_tac x = "Filter (%a. a:act A) $sch" in bexI)
prefer 2
apply (simp add: compositionality_sch)
apply (simp add: compatibility_consequence1 externals_of_par ext1_ext2_is_not_act1)
(* There is a schedule of B *)
apply (rule_tac x = "Filter (%a. a:act B) $sch" in bexI)
prefer 2
apply (simp add: compositionality_sch)
apply (simp add: compatibility_consequence2 externals_of_par ext1_ext2_is_not_act2)
(* Traces of A||B have only external actions from A or B *)
apply (rule ForallPFilterP)

(* <== *)

(* replace schA and schB by Cut(schA) and Cut(schB) *)
apply (drule exists_LastActExtsch)
apply assumption
apply (drule exists_LastActExtsch)
apply assumption
apply (erule exE)+
apply (erule conjE)+
(* Schedules of A(B) have only actions of A(B) *)
apply (drule scheds_in_sig)
apply assumption
apply (drule scheds_in_sig)
apply assumption

apply (rename_tac h1 h2 schA schB)
(* mksch is exactly the construction of trA||B out of schA, schB, and the oracle tr,
   we need here *)
apply (rule_tac x = "mksch A B$tr$schA$schB" in bexI)

(* External actions of mksch are just the oracle *)
apply (simp add: FilterA_mksch_is_tr)

(* mksch is a schedule -- use compositionality on sch-level *)
apply (simp add: compositionality_sch)
apply (simp add: FilterAmksch_is_schA FilterBmksch_is_schB)
apply (erule ForallAorB_mksch)
apply (erule ForallPForallQ)
apply (erule ext_is_act)
done



subsection {* COMPOSITIONALITY on TRACE Level -- for Modules *}

lemma compositionality_tr_modules: 

"!! A B. [| is_trans_of A; is_trans_of B; compatible A B; compatible B A;  
            is_asig(asig_of A); is_asig(asig_of B)|]  
 ==> Traces (A||B) = par_traces (Traces A) (Traces B)"

apply (unfold Traces_def par_traces_def)
apply (simp add: asig_of_par)
apply (rule set_eqI)
apply (simp add: compositionality_tr externals_of_par)
done


declaration {* fn _ => Simplifier.map_ss (Simplifier.set_mksym Simplifier.default_mk_sym) *}


end
