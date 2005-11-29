(* $Id$ *)

(* METHOD FOR ANALYSING EQUATION INVOLVING PERMUTATION *)

(* tries until depth 40 the following (in that order):                     *)
(*                                                                         *)
(*  - simplification plus analysing perm_swaps, perm_fresh_fresh, perm_bij *)
(*  - permutation compositions (on the left hand side of =)                *)
(*  - simplification of permutation on applications and abstractions       *)
(*  - analysing congruences (from Stefan Berghofer's datatype pkg)         *)
(*  - unfolding permutation on functions                                   *)
(*  - expanding equalities of functions                                    *)
(*                                                                         *)
(*  for supports - it first unfolds the definitions and strips of intros   *)

local

(* pulls out dynamically a thm via the simpset *)
fun dynamic_thm ss name = 
    ProofContext.get_thm (Simplifier.the_context ss) (Name name);

(* initial simplification step in the tactic *)
fun initial_simp_tac ss i =
    let
        (* these lemmas are created dynamically according to the atom types *) 
	val perm_swap  = dynamic_thm ss "perm_swap";
        val perm_fresh = dynamic_thm ss "perm_fresh_fresh";
        val perm_bij   = dynamic_thm ss "perm_bij";
        val ss' = ss addsimps [perm_swap,perm_fresh,perm_bij]
    in
      ("general simplification step", FIRST [rtac conjI i, asm_full_simp_tac ss' i])
    end;

(* applies the perm_compose rule - this rule would loop in the simplifier *)
fun apply_perm_compose_tac ss i = 
    let
	val perm_compose = dynamic_thm ss "perm_compose"; 
    in
	("analysing permutation compositions on the lhs",rtac (perm_compose RS trans)  i)
    end


(* applies the perm_eq_lam and perm_eq_app simplifications *)
fun apply_app_lam_simp_tac ss i =
    let 
	val perm_app_eq  = dynamic_thm ss "perm_app_eq";
        val perm_lam_eq  = thm "nominal.perm_eq_lam"
    in
     ("simplification of permutations on applications and lambdas", 
      asm_full_simp_tac (HOL_basic_ss addsimps [perm_app_eq,perm_lam_eq]) i)
    end

(* applying Stefan's smart congruence tac *)
fun apply_cong_tac i = 
    ("application of congruence",
     (fn st => DatatypeAux.cong_tac  i st handle Subscript => no_tac st));

(* unfolds the definition of permutations applied to functions *)
fun unfold_perm_fun_def_tac i = 
    let
	val perm_fun_def = thm "nominal.perm_fun_def"
    in
	("unfolding of permutations on functions", 
	 simp_tac (HOL_basic_ss addsimps [perm_fun_def]) i)
    end

(* applies the expand_fun_eq rule to the first goal and strips off all universal quantifiers *)
fun expand_fun_eq_tac i =    
    ("extensionality expansion of functions",
    EVERY [simp_tac (HOL_basic_ss addsimps [expand_fun_eq]) i, REPEAT_DETERM (rtac allI i)]);

(* debugging *)
fun DEBUG_tac (msg,tac) = 
    EVERY [CHANGED tac, print_tac ("after "^msg)]; 
fun NO_DEBUG_tac (_,tac) = CHANGED tac; 

(* Main Tactic *)

(* "repeating"-depth is set to 40 - this seems sufficient *)
fun perm_simp_tac tactical ss i = 
    DETERM (REPEAT_DETERM_N 40 
      (FIRST[tactical (initial_simp_tac ss i),
             tactical (apply_perm_compose_tac ss i),
             tactical (apply_app_lam_simp_tac ss i),
             tactical (apply_cong_tac i), 
             tactical (unfold_perm_fun_def_tac i),
             tactical (expand_fun_eq_tac i)]));

(* tactic that first unfolds the support definition *)
(* and strips of intros, then applies perm_simp_tac *)
fun supports_tac tactical ss i =
  let 
      val supports_def = thm "nominal.op supports_def";
      val fresh_def    = thm "nominal.fresh_def";
      val fresh_prod   = thm "nominal.fresh_prod";
      val simps        = [supports_def,symmetric fresh_def,fresh_prod]
  in
      EVERY [tactical ("unfolding of supports ",simp_tac (HOL_basic_ss addsimps simps) i),
             tactical ("stripping of foralls  " ,REPEAT_DETERM (rtac allI i)),
             tactical ("geting rid of the imps",rtac impI i),
             tactical ("eliminating conjuncts ",REPEAT_DETERM (etac  conjE i)),
             tactical ("applying perm_simp    ",perm_simp_tac tactical ss i)]
  end;

in             


fun simp_meth_setup tac =
  Method.only_sectioned_args (Simplifier.simp_modifiers' @ Splitter.split_modifiers)
  (Method.SIMPLE_METHOD' HEADGOAL o tac o local_simpset_of);

val perm_eq_meth        = simp_meth_setup (perm_simp_tac NO_DEBUG_tac);
val perm_eq_meth_debug  = simp_meth_setup (perm_simp_tac DEBUG_tac);
val supports_meth       = simp_meth_setup (supports_tac NO_DEBUG_tac);
val supports_meth_debug = simp_meth_setup (supports_tac DEBUG_tac);

end



