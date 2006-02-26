(* $Id$ *)

(* METHOD FOR ANALYSING EQUATION INVOLVING PERMUTATION *)

local

(* pulls out dynamically a thm via the simpset *)
fun dynamic_thms ss name = 
    ProofContext.get_thms (Simplifier.the_context ss) (Name name);
fun dynamic_thm ss name = 
    ProofContext.get_thm (Simplifier.the_context ss) (Name name);

(* FIXME: make it usable for all atom-types *)
(* initial simplification step in the tactic *)
fun perm_eval_tac ss i =
    let
        val perm_eq_app   = thm "nominal.pt_fun_app_eq";
        val at_inst       = dynamic_thm ss "at_name_inst";
        val pt_inst       = dynamic_thm ss "pt_name_inst";

        fun perm_eval_simproc sg ss redex =
        (case redex of 
        (* case pi o (f x) == (pi o f) (pi o x)    *)
        (* special treatment in cases of constants *)
        (Const("nominal.perm",Type("fun",[Type("List.list",[Type("*",[ty,_])]),_])) $ pi $ (f $ x)) 
        => let
             val _ = warning ("type: "^Sign.string_of_typ (sign_of (the_context())) ty)
           in

           (case f of
                    (* nothing to do on constants *)
                    (* FIXME: proper treatment of constants *)
                      Const(_,_)                   => NONE
                    | (Const(_,_) $ _)             => NONE
                    | ((Const(_,_) $ _) $ _)       => NONE
                    | (((Const(_,_) $ _) $ _) $ _) => NONE
                    | _ => 
                       (* FIXME: analyse type here or at "pty"*)
		       SOME ((at_inst RS (pt_inst RS perm_eq_app)) RS eq_reflection))
            end

        (* case pi o (%x. f x) == (%x. pi o (f ((rev pi)o x))) *)
        | (Const("nominal.perm",_) $ pi $ (Abs _)) 
        => let 
             val perm_fun_def = thm "nominal.perm_fun_def"
           in SOME (perm_fun_def) end

        (* no redex otherwise *) 
        | _ => NONE);

	val perm_eval =
	    Simplifier.simproc (Theory.sign_of (the_context ())) "perm_eval" 
	    ["nominal.perm pi x"] perm_eval_simproc;

        (* these lemmas are created dynamically according to the atom types *) 
	val perm_swap     = dynamic_thms ss "perm_swap";
        val perm_fresh    = dynamic_thms ss "perm_fresh_fresh";
        val perm_bij      = dynamic_thms ss "perm_bij";
        val perm_compose' = dynamic_thms ss "perm_compose'";
        val perm_pi_simp  = dynamic_thms ss "perm_pi_simp";
        val ss' = ss addsimps (perm_swap@perm_fresh@perm_bij@perm_compose'@perm_pi_simp)
                     addsimprocs [perm_eval];
                    
    in
      ("general simplification step", FIRST [rtac conjI i, asm_full_simp_tac ss' i])
    end;

(* applies the perm_compose rule - this rule would loop in the simplifier     *)
(* in case there are more atom-types we have to check every possible instance *)
(* of perm_compose                                                            *)
fun apply_perm_compose_tac ss i = 
    let
	val perm_compose = dynamic_thms ss "perm_compose"; 
        val tacs = map (fn thm => (rtac (thm RS trans) i)) perm_compose
    in
	("analysing permutation compositions on the lhs",FIRST (tacs))
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

fun perm_simp_tac tactical ss i = 
    DETERM (tactical (perm_eval_tac ss i));

(* perm_simp_tac plus additional tactics to decide            *)
(* support problems                                           *)
(* the "repeating"-depth is set to 40 - this seems sufficient *)
fun perm_supports_tac tactical ss i = 
    DETERM (REPEAT_DETERM_N 40 
      (FIRST[tactical (perm_eval_tac ss i),
             tactical (apply_perm_compose_tac ss i),
             tactical (apply_cong_tac i), 
             tactical (unfold_perm_fun_def_tac i),
             tactical (expand_fun_eq_tac i)]));

(* tactic that first unfolds the support definition          *)
(* and strips off the intros, then applies perm_supports_tac *)
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
             tactical ("applying perm_simp    ",perm_supports_tac tactical ss i)]
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



