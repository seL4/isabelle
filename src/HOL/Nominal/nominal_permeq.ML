(* $Id$ *)

(* METHOD FOR ANALYSING EQUATION INVOLVING PERMUTATION *)

local

(* applies the expand_fun_eq rule to the first goal and strips off all universal quantifiers *)
val Expand_Fun_Eq_tac =    
    ("extensionality on functions",
    EVERY [simp_tac (HOL_basic_ss addsimps [expand_fun_eq]) 1, REPEAT_DETERM (rtac allI 1)]);

(* applies the perm_compose rule - this rule would loop in the simplifier *)
fun Apply_Perm_Compose_tac ctxt = 
    let 
	val perm_compose = PureThy.get_thm (ProofContext.theory_of ctxt) (Name ("perm_compose"));
    in ("analysing permutation compositions",rtac (perm_compose RS trans)  1)
    end;

(* unfolds the definition of permutations applied to functions *)
fun Unfold_Perm_Fun_Def_tac ctxt = 
    let 
	val perm_fun_def = PureThy.get_thm (ProofContext.theory_of ctxt) (Name ("nominal.perm_fun_def"))
    in ("unfolding of perms on functions", simp_tac (HOL_basic_ss addsimps [perm_fun_def]) 1)
    end
    
(* applies the perm_eq_lam and perm_eq_app simplifications *)
fun Apply_SimProc_tac ctxt = 
    let
        val thy = ProofContext.theory_of ctxt;
	val perm_app_eq = PureThy.get_thm thy (Name ("perm_app_eq"));
        val perm_lam_eq = PureThy.get_thm thy (Name ("perm_eq_lam"));
    in
	("simplification of permutation on applications and lambdas", 
	 asm_full_simp_tac (HOL_basic_ss addsimps [perm_app_eq,perm_lam_eq]) 1)
    end;

(* applying Stefan's smart congruence tac *)
val Apply_Cong_tac = ("application of congruence",
                     (fn st => DatatypeAux.cong_tac  1 st handle Subscript => no_tac st));

(* initial simplification step in the tactic *)
fun Initial_Simp_tac thms ctxt =
    let
	val thy = ProofContext.theory_of ctxt;
	val perm_swap  = PureThy.get_thm thy (Name ("perm_swap"));
        val perm_fresh = PureThy.get_thm thy (Name ("perm_fresh_fresh"));
        val perm_bij   = PureThy.get_thm thy (Name ("perm_bij"));
        val simps = (local_simpset_of ctxt) addsimps (thms @ [perm_swap,perm_fresh,perm_bij])
    in
      ("general simplification step", FIRST [rtac conjI 1, asm_full_simp_tac simps 1])
    end;


(* debugging *)
fun DEBUG_tac (msg,tac) = 
    EVERY [print_tac ("before application of "^msg), CHANGED tac, print_tac ("after "^msg)]; 
fun NO_DEBUG_tac (_,tac) = CHANGED tac; 

(* Main Tactic *)
(* "repeating"-depth is set to 40 - this seems sufficient *)
fun perm_simp_tac tactical thms ctxt = 
    REPEAT_DETERM_N 40 
      (FIRST[tactical (Initial_Simp_tac thms ctxt),
             tactical (Apply_Perm_Compose_tac ctxt),
             tactical (Apply_SimProc_tac ctxt),
             tactical Apply_Cong_tac, 
             tactical (Unfold_Perm_Fun_Def_tac ctxt),
             tactical Expand_Fun_Eq_tac]);

(* tactic that unfolds first the support definition *)
(* and then applies perm_simp                       *)
fun supports_tac tactical thms ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val supports_def = PureThy.get_thm thy (Name ("nominal.op supports_def"));
    val fresh_def    = PureThy.get_thm thy (Name ("nominal.fresh_def"));
    val fresh_prod   = PureThy.get_thm thy (Name ("nominal.fresh_prod"));
    val simps        = [supports_def,symmetric fresh_def,fresh_prod];

  in
      EVERY [tactical ("unfolding of supports",simp_tac (HOL_basic_ss addsimps simps) 1),
             tactical ("stripping of foralls " ,REPEAT_DETERM (rtac allI 1)),
             tactical ("geting rid of the imp",rtac impI 1),
             tactical ("eliminating conjuncts",REPEAT_DETERM (etac  conjE 1)),
             tactical ("applying perm_simp   ",perm_simp_tac tactical thms ctxt)]
  end;

in             

val perm_eq_meth = 
    Method.thms_ctxt_args 
	(fn thms => fn ctxt => Method.SIMPLE_METHOD (DETERM (perm_simp_tac NO_DEBUG_tac thms ctxt)));

val perm_eq_meth_debug = 
    Method.thms_ctxt_args 
	(fn thms => fn ctxt => Method.SIMPLE_METHOD (DETERM (perm_simp_tac DEBUG_tac thms ctxt)));

val supports_meth = 
    Method.thms_ctxt_args 
	(fn thms => fn ctxt => Method.SIMPLE_METHOD (DETERM (supports_tac NO_DEBUG_tac thms ctxt)));

val supports_meth_debug = 
    Method.thms_ctxt_args 
	(fn thms => fn ctxt => Method.SIMPLE_METHOD (DETERM (supports_tac DEBUG_tac thms ctxt)));

end



