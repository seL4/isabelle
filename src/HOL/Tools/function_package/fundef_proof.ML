(*  Title:      HOL/Tools/function_package/fundef_proof.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions. 
Internal proofs.
*)


signature FUNDEF_PROOF =
sig

    val mk_partial_rules : theory -> FundefCommon.prep_result 
         -> thm -> FundefCommon.fundef_result
end


structure FundefProof : FUNDEF_PROOF = 
struct

open FundefLib
open FundefCommon
open FundefAbbrev

(* Theory dependencies *)
val subsetD = thm "subsetD"
val split_apply = thm "Product_Type.split"
val wf_induct_rule = thm "FunDef.wfP_induct_rule";
val Pair_inject = thm "Product_Type.Pair_inject";

val wf_in_rel = thm "FunDef.wf_in_rel";
val in_rel_def = thm "FunDef.in_rel_def";

val acc_induct_rule = thm "FunDef.accP_induct_rule"
val acc_downward = thm "FunDef.accP_downward"
val accI = thm "FunDef.accPI"

val acc_subset_induct = thm "FunDef.accP_subset_induct"

val conjunctionD1 = thm "conjunctionD1"
val conjunctionD2 = thm "conjunctionD2"


fun mk_psimp thy globals R f_iff graph_is_function clause valthm =
    let
      val Globals {domT, z, ...} = globals
                                   
      val ClauseInfo {qglr = (oqs, _, _, _), cdata = ClauseContext {qs, cqs, gs, lhs, rhs, ags, ...}, ...} = clause
      val lhs_acc = cterm_of thy (Trueprop (mk_acc domT R $ lhs)) (* "acc R lhs" *)
      val z_smaller = cterm_of thy (Trueprop (R $ z $ lhs)) (* "R z lhs" *)
    in
      ((assume z_smaller) RS ((assume lhs_acc) RS acc_downward))
        |> (fn it => it COMP graph_is_function)
        |> implies_intr z_smaller
        |> forall_intr (cterm_of thy z)
        |> (fn it => it COMP valthm)
        |> implies_intr lhs_acc 
        |> asm_simplify (HOL_basic_ss addsimps [f_iff])
        |> fold_rev (implies_intr o cprop_of) ags
        |> fold_rev forall_intr_rename (map fst oqs ~~ cqs)
    end



fun mk_partial_induct_rule thy globals R complete_thm clauses =
    let
      val Globals {domT, x, z, a, P, D, ...} = globals
      val acc_R = mk_acc domT R
                  
      val x_D = assume (cterm_of thy (Trueprop (D $ x)))
      val a_D = cterm_of thy (Trueprop (D $ a))
                
      val D_subset = cterm_of thy (mk_forall x (implies $ Trueprop (D $ x) $ Trueprop (acc_R $ x)))
                     
      val D_dcl = (* "!!x z. [| x: D; (z,x):R |] ==> z:D" *)
                    mk_forall x
                    (mk_forall z (Logic.mk_implies (Trueprop (D $ x),
                                                    Logic.mk_implies (Trueprop (R $ z $ x),
                                                                      Trueprop (D $ z)))))
                    |> cterm_of thy
                    
                    
  (* Inductive Hypothesis: !!z. (z,x):R ==> P z *)
      val ihyp = all domT $ Abs ("z", domT, 
               implies $ Trueprop (R $ Bound 0 $ x)
             $ Trueprop (P $ Bound 0))
           |> cterm_of thy

      val aihyp = assume ihyp

  fun prove_case clause =
      let
    val ClauseInfo {cdata = ClauseContext {qs, cqs, ags, gs, lhs, rhs, case_hyp, ...}, RCs, 
                    qglr = (oqs, _, _, _), ...} = clause
                       
    val replace_x_ss = HOL_basic_ss addsimps [case_hyp]
    val lhs_D = simplify replace_x_ss x_D (* lhs : D *)
    val sih = full_simplify replace_x_ss aihyp
          
    fun mk_Prec (RCInfo {llRI, RIvs, CCas, rcarg, ...}) =
        sih |> forall_elim (cterm_of thy rcarg)
            |> implies_elim_swp llRI
            |> fold_rev (implies_intr o cprop_of) CCas
            |> fold_rev (forall_intr o cterm_of thy o Free) RIvs
        
    val P_recs = map mk_Prec RCs   (*  [P rec1, P rec2, ... ]  *)
                 
    val step = Trueprop (P $ lhs)
            |> fold_rev (curry Logic.mk_implies o prop_of) P_recs
            |> fold_rev (curry Logic.mk_implies) gs
            |> curry Logic.mk_implies (Trueprop (D $ lhs))
            |> fold_rev mk_forall_rename (map fst oqs ~~ qs)
            |> cterm_of thy
         
    val P_lhs = assume step
           |> fold forall_elim cqs
           |> implies_elim_swp lhs_D 
           |> fold_rev implies_elim_swp ags
           |> fold implies_elim_swp P_recs
          
    val res = cterm_of thy (Trueprop (P $ x))
           |> Simplifier.rewrite replace_x_ss
           |> symmetric (* P lhs == P x *)
           |> (fn eql => equal_elim eql P_lhs) (* "P x" *)
           |> implies_intr (cprop_of case_hyp)
           |> fold_rev (implies_intr o cprop_of) ags
           |> fold_rev forall_intr cqs
      in
    (res, step)
      end

  val (cases, steps) = split_list (map prove_case clauses)

  val istep = complete_thm
                |> forall_elim_vars 0
                |> fold (curry op COMP) cases (*  P x  *)
                |> implies_intr ihyp
                |> implies_intr (cprop_of x_D)
                |> forall_intr (cterm_of thy x)
         
  val subset_induct_rule = 
      acc_subset_induct
        |> (curry op COMP) (assume D_subset)
        |> (curry op COMP) (assume D_dcl)
        |> (curry op COMP) (assume a_D)
        |> (curry op COMP) istep
        |> fold_rev implies_intr steps
        |> implies_intr a_D
        |> implies_intr D_dcl
        |> implies_intr D_subset

  val subset_induct_all = fold_rev (forall_intr o cterm_of thy) [P, a, D] subset_induct_rule

  val simple_induct_rule =
      subset_induct_rule
        |> forall_intr (cterm_of thy D)
        |> forall_elim (cterm_of thy acc_R)
        |> assume_tac 1 |> Seq.hd
        |> (curry op COMP) (acc_downward
                              |> (instantiate' [SOME (ctyp_of thy domT)]
                                               (map (SOME o cterm_of thy) [R, x, z]))
                              |> forall_intr (cterm_of thy z)
                              |> forall_intr (cterm_of thy x))
        |> forall_intr (cterm_of thy a)
        |> forall_intr (cterm_of thy P)
    in
      (subset_induct_all, simple_induct_rule)
    end



(* Does this work with Guards??? *)
fun mk_domain_intro thy globals R R_cases clause =
    let
      val Globals {z, domT, ...} = globals
      val ClauseInfo {cdata = ClauseContext {qs, gs, lhs, rhs, cqs, ...}, 
                      qglr = (oqs, _, _, _), ...} = clause
      val goal = Trueprop (mk_acc domT R $ lhs)
                          |> fold_rev (curry Logic.mk_implies) gs
                          |> cterm_of thy
    in
      Goal.init goal 
      |> (SINGLE (resolve_tac [accI] 1)) |> the
      |> (SINGLE (eresolve_tac [forall_elim_vars 0 R_cases] 1))  |> the
      |> (SINGLE (CLASIMPSET auto_tac)) |> the
      |> Goal.conclude
      |> fold_rev forall_intr_rename (map fst oqs ~~ cqs)
    end


fun maybe_mk_domain_intro thy =
    if !FundefCommon.domintros then mk_domain_intro thy
    else K (K (K (K refl)))


fun mk_nest_term_case thy globals R' ihyp clause =
    let
      val Globals {x, z, ...} = globals
      val ClauseInfo {cdata = ClauseContext {qs,cqs,ags,lhs,rhs,case_hyp,...},tree,
                      qglr=(oqs, _, _, _), ...} = clause
          
      val ih_case = full_simplify (HOL_basic_ss addsimps [case_hyp]) ihyp
                    
      fun step (fixes, assumes) (_ $ arg) u (sub,(hyps,thms)) = 
          let
            val used = map (fn ((f,a),thm) => FundefCtxTree.export_thm thy (f, map prop_of a) thm) (u @ sub)
                       
            val hyp = Trueprop (R' $ arg $ lhs)
                      |> fold_rev (curry Logic.mk_implies o prop_of) used
                      |> FundefCtxTree.export_term (fixes, map prop_of assumes) 
                      |> fold_rev (curry Logic.mk_implies o prop_of) ags
                      |> fold_rev mk_forall_rename (map fst oqs ~~ qs)
                      |> cterm_of thy
                      
            val thm = assume hyp
                      |> fold forall_elim cqs
                      |> fold implies_elim_swp ags
                      |> FundefCtxTree.import_thm thy (fixes, assumes) (*  "(arg, lhs) : R'"  *)
                      |> fold implies_elim_swp used
                      
            val acc = thm COMP ih_case
                      
            val z_eq_arg = cterm_of thy (Trueprop (HOLogic.mk_eq (z, arg)))
                           
            val arg_eq_z = (assume z_eq_arg) RS sym
                           
            val z_acc = simplify (HOL_basic_ss addsimps [arg_eq_z]) acc (* fragile, slow... *)
                        |> implies_intr (cprop_of case_hyp)
                        |> implies_intr z_eq_arg

            val z_eq_arg = assume (cterm_of thy (Trueprop (mk_eq (z, arg))))
            val x_eq_lhs = assume (cterm_of thy (Trueprop (mk_eq (x, lhs))))
                           
            val ethm = (z_acc OF [z_eq_arg, x_eq_lhs])
                         |> FundefCtxTree.export_thm thy (fixes, 
                                                          prop_of z_eq_arg :: prop_of x_eq_lhs :: map prop_of (ags @ assumes))
                         |> fold_rev forall_intr_rename (map fst oqs ~~ cqs)

            val sub' = sub @ [(([],[]), acc)]
          in
            (sub', (hyp :: hyps, ethm :: thms))
          end
        | step _ _ _ _ = raise Match
    in
      FundefCtxTree.traverse_tree step tree
    end
    
    
fun mk_nest_term_rule thy globals R R_cases clauses =
    let
      val Globals { domT, x, z, ... } = globals
      val acc_R = mk_acc domT R
                  
      val R' = Free ("R", fastype_of R)
               
      val Rrel = Free ("R", mk_relT (domT, domT))
      val inrel_R = Const ("FunDef.in_rel", mk_relT (domT, domT) --> fastype_of R) $ Rrel
                    
      val wfR' = cterm_of thy (Trueprop (Const ("FunDef.wfP", (domT --> domT --> boolT) --> boolT) $ R')) (* "wf R'" *)
                          
      (* Inductive Hypothesis: !!z. (z,x):R' ==> z : acc R *)
      val ihyp = all domT $ Abs ("z", domT, 
                                 implies $ Trueprop (R' $ Bound 0 $ x)
                                         $ Trueprop (acc_R $ Bound 0))
                     |> cterm_of thy

      val ihyp_a = assume ihyp |> forall_elim_vars 0
                   
      val R_z_x = cterm_of thy (Trueprop (R $ z $ x)) 
                  
      val (hyps,cases) = fold (mk_nest_term_case thy globals R' ihyp_a) clauses ([],[])
    in
      R_cases
        |> forall_elim (cterm_of thy z)
        |> forall_elim (cterm_of thy x)
        |> forall_elim (cterm_of thy (acc_R $ z))
        |> curry op COMP (assume R_z_x)
        |> fold_rev (curry op COMP) cases
        |> implies_intr R_z_x
        |> forall_intr (cterm_of thy z)
        |> (fn it => it COMP accI)
        |> implies_intr ihyp
        |> forall_intr (cterm_of thy x)
        |> (fn it => Drule.compose_single(it,2,wf_induct_rule))
        |> curry op RS (assume wfR')
        |> fold implies_intr hyps
        |> implies_intr wfR'
        |> forall_intr (cterm_of thy R')
        |> forall_elim (cterm_of thy (inrel_R))
        |> curry op RS wf_in_rel
        |> full_simplify (HOL_basic_ss addsimps [in_rel_def])
        |> forall_intr (cterm_of thy Rrel)
    end
    



fun mk_partial_rules thy data provedgoal =
    let
      val Prep {globals, G, f, R, clauses, values, R_cases, ex1_iff, ...} = data
                                                                            
      val provedgoal = PROFILE "Closing result" Goal.close_result provedgoal
                       
      val graph_is_function = PROFILE "Getting function theorem" (fn x => (x COMP conjunctionD1) |> forall_elim_vars 0) provedgoal
                              
      val complete_thm = PROFILE "Getting cases" (curry op COMP provedgoal) conjunctionD2

      val f_iff = PROFILE "Making f_iff" (curry op RS graph_is_function) ex1_iff
                  
      val psimps = PROFILE "Proving simplification rules" (map2 (mk_psimp thy globals R f_iff graph_is_function)) clauses values
                    
      val (subset_pinduct, simple_pinduct) = PROFILE "Proving partial induction rule" 
                                             (mk_partial_induct_rule thy globals R complete_thm) clauses
                                             
      val total_intro = PROFILE "Proving nested termination rule" (mk_nest_term_rule thy globals R R_cases) clauses
                        
      val dom_intros = PROFILE "Proving domain introduction rules" (map (maybe_mk_domain_intro thy globals R R_cases)) clauses
    in 
      FundefResult {f=f, G=G, R=R, completeness=complete_thm, 
                    psimps=psimps, subset_pinduct=subset_pinduct, simple_pinduct=simple_pinduct, total_intro=total_intro,
                    dom_intros=dom_intros}
    end
    
    
end


