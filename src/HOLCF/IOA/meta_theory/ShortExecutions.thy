(*  Title:      HOLCF/IOA/meta_theory/ShortExecutions.thy
    ID:         $Id$
    Author:     Olaf Müller
*)

theory ShortExecutions
imports Traces
begin

text {*
  Some properties about @{text "Cut ex"}, defined as follows:

  For every execution ex there is another shorter execution @{text "Cut ex"}
  that has the same trace as ex, but its schedule ends with an external action.
*}

consts

(*  LastActExtex      ::"('a,'s)ioa => ('a,'s) pairs  => bool"*)
  LastActExtsch     ::"('a,'s)ioa => 'a Seq         => bool"

  Cut               ::"('a => bool) => 'a Seq    => 'a Seq"

  oraclebuild       ::"('a => bool) => 'a Seq -> 'a Seq -> 'a Seq"

defs

LastActExtsch_def:
  "LastActExtsch A sch == (Cut (%x. x: ext A) sch = sch)"

(* LastActExtex_def:
  "LastActExtex A ex == LastActExtsch A (filter_act$ex)" *)

Cut_def:
  "Cut P s == oraclebuild P$s$(Filter P$s)"

oraclebuild_def:
  "oraclebuild P == (fix$(LAM h s t. case t of
       nil => nil
    | x##xs =>
      (case x of
        UU => UU
      | Def y => (Takewhile (%x.~P x)$s)
                  @@ (y>>(h$(TL$(Dropwhile (%x.~ P x)$s))$xs))
      )
    ))"


axioms

Cut_prefixcl_Finite:
  "Finite s ==> (? y. s = Cut P s @@ y)"

LastActExtsmall1:
  "LastActExtsch A sch ==> LastActExtsch A (TL$(Dropwhile P$sch))"

LastActExtsmall2:
  "[| Finite sch1; LastActExtsch A (sch1 @@ sch2) |] ==> LastActExtsch A sch2"



ML {*
fun thin_tac' j =
  rotate_tac (j - 1) THEN'
  etac thin_rl THEN'
  rotate_tac (~ (j - 1))
*}


subsection "oraclebuild rewrite rules"


lemma oraclebuild_unfold:
"oraclebuild P = (LAM s t. case t of 
       nil => nil
    | x##xs => 
      (case x of
        UU => UU
      | Def y => (Takewhile (%a.~ P a)$s)
                  @@ (y>>(oraclebuild P$(TL$(Dropwhile (%a.~ P a)$s))$xs))
      )
    )"
apply (rule trans)
apply (rule fix_eq2)
apply (rule oraclebuild_def)
apply (rule beta_cfun)
apply simp
done

lemma oraclebuild_UU: "oraclebuild P$sch$UU = UU"
apply (subst oraclebuild_unfold)
apply simp
done

lemma oraclebuild_nil: "oraclebuild P$sch$nil = nil"
apply (subst oraclebuild_unfold)
apply simp
done

lemma oraclebuild_cons: "oraclebuild P$s$(x>>t) =  
          (Takewhile (%a.~ P a)$s)    
           @@ (x>>(oraclebuild P$(TL$(Dropwhile (%a.~ P a)$s))$t))"
apply (rule trans)
apply (subst oraclebuild_unfold)
apply (simp add: Consq_def)
apply (simp add: Consq_def)
done


subsection "Cut rewrite rules"

lemma Cut_nil: 
"[| Forall (%a.~ P a) s; Finite s|]  
            ==> Cut P s =nil"
apply (unfold Cut_def)
apply (subgoal_tac "Filter P$s = nil")
apply (simp (no_asm_simp) add: oraclebuild_nil)
apply (rule ForallQFilterPnil)
apply assumption+
done

lemma Cut_UU: 
"[| Forall (%a.~ P a) s; ~Finite s|]  
            ==> Cut P s =UU"
apply (unfold Cut_def)
apply (subgoal_tac "Filter P$s= UU")
apply (simp (no_asm_simp) add: oraclebuild_UU)
apply (rule ForallQFilterPUU)
apply assumption+
done

lemma Cut_Cons: 
"[| P t;  Forall (%x.~ P x) ss; Finite ss|]  
            ==> Cut P (ss @@ (t>> rs))  
                 = ss @@ (t >> Cut P rs)"
apply (unfold Cut_def)
apply (simp add: ForallQFilterPnil oraclebuild_cons TakewhileConc DropwhileConc)
done


subsection "Cut lemmas for main theorem"

lemma FilterCut: "Filter P$s = Filter P$(Cut P s)"
apply (rule_tac A1 = "%x. True" and Q1 = "%x.~ P x" and x1 = "s" in take_lemma_induct [THEN mp])
prefer 3 apply (fast)
apply (case_tac "Finite s")
apply (simp add: Cut_nil ForallQFilterPnil)
apply (simp add: Cut_UU ForallQFilterPUU)
(* main case *)
apply (simp add: Cut_Cons ForallQFilterPnil)
done


lemma Cut_idemp: "Cut P (Cut P s) = (Cut P s)"
apply (rule_tac A1 = "%x. True" and Q1 = "%x.~ P x" and x1 = "s" in
  take_lemma_less_induct [THEN mp])
prefer 3 apply (fast)
apply (case_tac "Finite s")
apply (simp add: Cut_nil ForallQFilterPnil)
apply (simp add: Cut_UU ForallQFilterPUU)
(* main case *)
apply (simp add: Cut_Cons ForallQFilterPnil)
apply (rule take_reduction)
apply auto
done


lemma MapCut: "Map f$(Cut (P o f) s) = Cut P (Map f$s)"
apply (rule_tac A1 = "%x. True" and Q1 = "%x.~ P (f x) " and x1 = "s" in
  take_lemma_less_induct [THEN mp])
prefer 3 apply (fast)
apply (case_tac "Finite s")
apply (simp add: Cut_nil)
apply (rule Cut_nil [symmetric])
apply (simp add: ForallMap o_def)
apply (simp add: Map2Finite)
(* csae ~ Finite s *)
apply (simp add: Cut_UU)
apply (rule Cut_UU)
apply (simp add: ForallMap o_def)
apply (simp add: Map2Finite)
(* main case *)
apply (simp add: Cut_Cons MapConc ForallMap FiniteMap1 o_def)
apply (rule take_reduction)
apply auto
done


lemma Cut_prefixcl_nFinite [rule_format (no_asm)]: "~Finite s --> Cut P s << s"
apply (intro strip)
apply (rule take_lemma_less [THEN iffD1])
apply (intro strip)
apply (rule mp)
prefer 2 apply (assumption)
apply (tactic "thin_tac' 1 1")
apply (rule_tac x = "s" in spec)
apply (rule nat_less_induct)
apply (intro strip)
apply (rename_tac na n s)
apply (case_tac "Forall (%x. ~ P x) s")
apply (rule take_lemma_less [THEN iffD2, THEN spec])
apply (simp add: Cut_UU)
(* main case *)
apply (drule divide_Seq3)
apply (erule exE)+
apply (erule conjE)+
apply hypsubst
apply (simp add: Cut_Cons)
apply (rule take_reduction_less)
(* auto makes also reasoning about Finiteness of parts of s ! *)
apply auto
done


lemma execThruCut: "!!ex .is_exec_frag A (s,ex) ==> is_exec_frag A (s,Cut P ex)"
apply (case_tac "Finite ex")
apply (cut_tac s = "ex" and P = "P" in Cut_prefixcl_Finite)
apply assumption
apply (erule exE)
apply (rule exec_prefix2closed)
apply (erule_tac s = "ex" and t = "Cut P ex @@ y" in subst)
apply assumption
apply (erule exec_prefixclosed)
apply (erule Cut_prefixcl_nFinite)
done


subsection "Main Cut Theorem"

lemma exists_LastActExtsch: 
 "[|sch : schedules A ; tr = Filter (%a. a:ext A)$sch|]  
    ==> ? sch. sch : schedules A &  
               tr = Filter (%a. a:ext A)$sch & 
               LastActExtsch A sch"

apply (unfold schedules_def has_schedule_def)
apply (tactic "safe_tac set_cs")
apply (rule_tac x = "filter_act$ (Cut (%a. fst a:ext A) (snd ex))" in exI)
apply (simp add: executions_def)
apply (tactic {* pair_tac "ex" 1 *})
apply (tactic "safe_tac set_cs")
apply (rule_tac x = " (x,Cut (%a. fst a:ext A) y) " in exI)
apply (simp (no_asm_simp))

(* Subgoal 1: Lemma:  propagation of execution through Cut *)

apply (simp add: execThruCut)

(* Subgoal 2:  Lemma:  Filter P s = Filter P (Cut P s) *)

apply (simp (no_asm) add: filter_act_def)
apply (subgoal_tac "Map fst$ (Cut (%a. fst a: ext A) y) = Cut (%a. a:ext A) (Map fst$y) ")

apply (rule_tac [2] MapCut [unfolded o_def])
apply (simp add: FilterCut [symmetric])

(* Subgoal 3: Lemma: Cut idempotent  *)

apply (simp (no_asm) add: LastActExtsch_def filter_act_def)
apply (subgoal_tac "Map fst$ (Cut (%a. fst a: ext A) y) = Cut (%a. a:ext A) (Map fst$y) ")
apply (rule_tac [2] MapCut [unfolded o_def])
apply (simp add: Cut_idemp)
done


subsection "Further Cut lemmas"

lemma LastActExtimplnil: 
  "[| LastActExtsch A sch; Filter (%x. x:ext A)$sch = nil |]  
    ==> sch=nil"
apply (unfold LastActExtsch_def)
apply (drule FilternPnilForallP)
apply (erule conjE)
apply (drule Cut_nil)
apply assumption
apply simp
done

lemma LastActExtimplUU: 
  "[| LastActExtsch A sch; Filter (%x. x:ext A)$sch = UU |]  
    ==> sch=UU"
apply (unfold LastActExtsch_def)
apply (drule FilternPUUForallP)
apply (erule conjE)
apply (drule Cut_UU)
apply assumption
apply simp
done

end
