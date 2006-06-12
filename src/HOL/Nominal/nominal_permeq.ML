(*  Title:      HOL/Nominal/nominal_permeq.ML
    ID:         $Id$
    Author:     Christian Urban, TU Muenchen

Methods for simplifying permutations and
for analysing equations involving permutations.
*)

local

(* pulls out dynamically a thm via the simpset *)
fun dynamic_thms ss name = ProofContext.get_thms (Simplifier.the_context ss) (Name name);
fun dynamic_thm ss name = ProofContext.get_thm (Simplifier.the_context ss) (Name name);

(* a tactic simplyfying permutations *)
val perm_fun_def = thm "Nominal.perm_fun_def"
val perm_eq_app = thm "Nominal.pt_fun_app_eq"

fun perm_eval_tac ss i =
    let
        fun perm_eval_simproc sg ss redex =
        let 
	   (* the "application" case below is only applicable when the head   *)
           (* of f is not a constant  or when it is a permuattion with two or *) 
           (* more arguments                                                  *)
           fun applicable t = 
	       (case (strip_comb t) of
		  (Const ("Nominal.perm",_),ts) => (length ts) >= 2
		| (Const _,_) => false
		| _ => true)

	in
        (case redex of 
        (* case pi o (f x) == (pi o f) (pi o x)          *)
        (* special treatment according to the head of f  *)
        (Const("Nominal.perm",
          Type("fun",[Type("List.list",[Type("*",[Type(n,_),_])]),_])) $ pi $ (f $ x)) => 
	   (case (applicable f) of
                false => NONE  
              | _ => 
		let
		    val name = Sign.base_name n
		    val at_inst     = dynamic_thm ss ("at_"^name^"_inst")
		    val pt_inst     = dynamic_thm ss ("pt_"^name^"_inst")  
		in SOME ((at_inst RS (pt_inst RS perm_eq_app)) RS eq_reflection) end)

        (* case pi o (%x. f x) == (%x. pi o (f ((rev pi)o x))) *)
        | (Const("Nominal.perm",_) $ pi $ (Abs _)) => SOME (perm_fun_def)

        (* no redex otherwise *) 
        | _ => NONE) end

	val perm_eval =
	    Simplifier.simproc (Theory.sign_of (the_context ())) "perm_eval" 
	    ["Nominal.perm pi x"] perm_eval_simproc;

      (* these lemmas are created dynamically according to the atom types *) 
      val perm_swap        = dynamic_thms ss "perm_swap"
      val perm_fresh       = dynamic_thms ss "perm_fresh_fresh"
      val perm_bij         = dynamic_thms ss "perm_bij"
      val perm_pi_simp     = dynamic_thms ss "perm_pi_simp"
      val ss' = ss addsimps (perm_swap@perm_fresh@perm_bij@perm_pi_simp)
    in
	("general simplification step", asm_full_simp_tac (ss' addsimprocs [perm_eval]) i)
    end;

(* applies the perm_compose rule such that                             *)
(*                                                                     *)
(*   pi o (pi' o lhs) = rhs                                            *)
(*                                                                     *)
(* is transformed to                                                   *) 
(*                                                                     *)
(*  (pi o pi') o (pi' o lhs) = rhs                                     *)
(*                                                                     *)
(* this rule would loop in the simplifier, so some trick is used with  *)
(* generating perm_aux'es for the outermost permutation and then un-   *)
(* folding the definition                                              *)
val pt_perm_compose_aux = thm "pt_perm_compose_aux";
val cp1_aux             = thm "cp1_aux";
val perm_aux_fold       = thm "perm_aux_fold"; 

fun perm_compose_tac ss i = 
    let
	fun perm_compose_simproc sg ss redex =
	(case redex of
           (Const ("Nominal.perm", Type ("fun", [Type ("List.list", 
             [Type ("*", [T as Type (tname,_),_])]),_])) $ pi1 $ (Const ("Nominal.perm", 
               Type ("fun", [Type ("List.list", [Type ("*", [U as Type (uname,_),_])]),_])) $ 
                pi2 $ t)) =>
        let
	    val tname' = Sign.base_name tname
            val uname' = Sign.base_name uname
        in
            if pi1 <> pi2 then  (* only apply the composition rule in this case *)
               if T = U then    
                SOME (Drule.instantiate'
	              [SOME (ctyp_of sg (fastype_of t))]
		      [SOME (cterm_of sg pi1), SOME (cterm_of sg pi2), SOME (cterm_of sg t)]
		      (mk_meta_eq ([PureThy.get_thm sg (Name ("pt_"^tname'^"_inst")),
	               PureThy.get_thm sg (Name ("at_"^tname'^"_inst"))] MRS pt_perm_compose_aux)))
               else
                SOME (Drule.instantiate'
	              [SOME (ctyp_of sg (fastype_of t))]
		      [SOME (cterm_of sg pi1), SOME (cterm_of sg pi2), SOME (cterm_of sg t)]
		      (mk_meta_eq (PureThy.get_thm sg (Name ("cp_"^tname'^"_"^uname'^"_inst")) RS 
                       cp1_aux)))
            else NONE
        end
       | _ => NONE);
	  
      val perm_compose  =
	Simplifier.simproc (the_context()) "perm_compose" 
	["Nominal.perm pi1 (Nominal.perm pi2 t)"] perm_compose_simproc;

      val ss' = Simplifier.theory_context (the_context ()) empty_ss	  

    in
	("analysing permutation compositions on the lhs",
         EVERY [rtac trans i,
                asm_full_simp_tac (ss' addsimprocs [perm_compose]) i,
                asm_full_simp_tac (HOL_basic_ss addsimps [perm_aux_fold]) i])
    end

(* applying Stefan's smart congruence tac *)
fun apply_cong_tac i = 
    ("application of congruence",
     (fn st => DatatypeAux.cong_tac i st handle Subscript => no_tac st));

(* unfolds the definition of permutations     *)
(* applied to functions such that             *)
(*                                            *)
(*   pi o f = rhs                             *)  
(*                                            *)
(* is transformed to                          *)
(*                                            *)
(*   %x. pi o (f ((rev pi) o x)) = rhs        *)
fun unfold_perm_fun_def_tac i = 
    let
	val perm_fun_def = thm "Nominal.perm_fun_def"
    in
	("unfolding of permutations on functions", 
         rtac (perm_fun_def RS meta_eq_to_obj_eq RS trans) i)
    end

(* applies the ext-rule such that      *)
(*                                     *)
(*    f = g    goes to /\x. f x = g x  *)
fun ext_fun_tac i = ("extensionality expansion of functions", rtac ext i);

(* FIXME FIXME FIXME *)
(* should be able to analyse pi o fresh_fun () = fresh_fun instances *) 
fun fresh_fun_eqvt_tac i =
    let
	val fresh_fun_equiv = thm "Nominal.fresh_fun_equiv_ineq"
    in
	("fresh_fun equivariance", rtac (fresh_fun_equiv RS trans) i)
    end		       
		       
(* debugging *)
fun DEBUG_tac (msg,tac) = 
    CHANGED (EVERY [tac, print_tac ("after "^msg)]); 
fun NO_DEBUG_tac (_,tac) = CHANGED tac; 

(* Main Tactics *)
fun perm_simp_tac tactical ss i = 
    DETERM (tactical (perm_eval_tac ss i));

(* perm_full_simp_tac is perm_simp_tac plus additional tactics    *)
(* to decide equation that come from support problems             *)
(* since it contains looping rules the "recursion" - depth is set *)
(* to 10 - this seems to be sufficient in most cases              *)
fun perm_full_simp_tac tactical ss =
  let fun perm_full_simp_tac_aux tactical ss n = 
	  if n=0 then K all_tac
	  else DETERM o 
	       (FIRST'[fn i => tactical ("splitting conjunctions on the rhs", rtac conjI i),
                       fn i => tactical (perm_eval_tac ss i),
		       fn i => tactical (perm_compose_tac ss i),
		       fn i => tactical (apply_cong_tac i), 
                       fn i => tactical (unfold_perm_fun_def_tac i),
                       fn i => tactical (ext_fun_tac i), 
                       fn i => tactical (fresh_fun_eqvt_tac i)]
		      THEN_ALL_NEW (TRY o (perm_full_simp_tac_aux tactical ss (n-1))))
  in perm_full_simp_tac_aux tactical ss 10 end;

(* tactic that first unfolds the support definition           *)
(* and strips off the intros, then applies perm_full_simp_tac *)
fun supports_tac tactical ss i =
  let 
      val supports_def = thm "Nominal.op supports_def";
      val fresh_def    = thm "Nominal.fresh_def";
      val fresh_prod   = thm "Nominal.fresh_prod";
      val simps        = [supports_def,symmetric fresh_def,fresh_prod]
  in
      EVERY [tactical ("unfolding of supports   ", simp_tac (HOL_basic_ss addsimps simps) i),
             tactical ("stripping of foralls    ", REPEAT_DETERM (rtac allI i)),
             tactical ("geting rid of the imps  ", rtac impI i),
             tactical ("eliminating conjuncts   ", REPEAT_DETERM (etac  conjE i)),
             tactical ("applying perm_full_simp ", perm_full_simp_tac tactical ss i
                                                   (*perm_simp_tac tactical ss i*))]
  end;


(* tactic that guesses the finite-support of a goal       *)
(* it collects all free variables and tries to show       *)
(* that the support of these free variables (op supports) *)
(* the goal                                               *)
fun collect_vars i (Bound j) vs = if j < i then vs else Bound (j - i) ins vs
  | collect_vars i (v as Free _) vs = v ins vs
  | collect_vars i (v as Var _) vs = v ins vs
  | collect_vars i (Const _) vs = vs
  | collect_vars i (Abs (_, _, t)) vs = collect_vars (i+1) t vs
  | collect_vars i (t $ u) vs = collect_vars i u (collect_vars i t vs);

val supports_rule = thm "supports_finite";

fun finite_guess_tac tactical ss i st =
    let val goal = List.nth(cprems_of st, i-1)
    in
      case Logic.strip_assums_concl (term_of goal) of
          _ $ (Const ("op :", _) $ (Const ("Nominal.supp", T) $ x) $
            Const ("Finite_Set.Finites", _)) =>
          let
            val cert = Thm.cterm_of (sign_of_thm st);
            val ps = Logic.strip_params (term_of goal);
            val Ts = rev (map snd ps);
            val vs = collect_vars 0 x [];
            val s = foldr (fn (v, s) =>
                HOLogic.pair_const (fastype_of1 (Ts, v)) (fastype_of1 (Ts, s)) $ v $ s)
              HOLogic.unit vs;
            val s' = list_abs (ps,
              Const ("Nominal.supp", fastype_of1 (Ts, s) --> body_type T) $ s);
            val supports_rule' = Thm.lift_rule goal supports_rule;
            val _ $ (_ $ S $ _) =
              Logic.strip_assums_concl (hd (prems_of supports_rule'));
            val supports_rule'' = Drule.cterm_instantiate
              [(cert (head_of S), cert s')] supports_rule'
          in
            (tactical ("guessing of the right supports-set",
                      EVERY [compose_tac (false, supports_rule'', 2) i,
                             asm_full_simp_tac ss (i+1),
                             supports_tac tactical ss i])) st
          end
        | _ => Seq.empty
    end
    handle Subscript => Seq.empty

val supports_fresh_rule = thm "supports_fresh";

fun fresh_guess_tac tactical ss i st =
    let 
	val goal = List.nth(cprems_of st, i-1)
    in
      case Logic.strip_assums_concl (term_of goal) of
          _ $ (Const ("Nominal.fresh", Type ("fun", [T, _])) $ _ $ t) => 
          let
            val cert = Thm.cterm_of (sign_of_thm st);
            val ps = Logic.strip_params (term_of goal);
            val Ts = rev (map snd ps);
            val vs = collect_vars 0 t [];
            val s = foldr (fn (v, s) =>
                HOLogic.pair_const (fastype_of1 (Ts, v)) (fastype_of1 (Ts, s)) $ v $ s)
              HOLogic.unit vs;
            val s' = list_abs (ps,
              Const ("Nominal.supp", fastype_of1 (Ts, s) --> (HOLogic.mk_setT T)) $ s);
            val supports_fresh_rule' = Thm.lift_rule goal supports_fresh_rule;
            val _ $ (_ $ S $ _) =
              Logic.strip_assums_concl (hd (prems_of supports_fresh_rule'));
            val supports_fresh_rule'' = Drule.cterm_instantiate
              [(cert (head_of S), cert s')] supports_fresh_rule'
            val fresh_def   = thm "Nominal.fresh_def";
	    val fresh_prod  = thm "Nominal.fresh_prod";
            val fresh_unit  = thm "Nominal.fresh_unit";
	    val simps       = [symmetric fresh_def,fresh_prod,fresh_unit]
          in
            (tactical ("guessing of the right set that supports the goal",
                      EVERY [compose_tac (false, supports_fresh_rule'', 3) i,
                             asm_full_simp_tac (ss addsimps simps) (i+2),
                             asm_full_simp_tac ss (i+1), 
                             supports_tac tactical ss i])) st
          end
        | _ => Seq.empty
    end
    handle Subscript => Seq.empty

in             

fun simp_meth_setup tac =
  Method.only_sectioned_args (Simplifier.simp_modifiers' @ Splitter.split_modifiers)
  (Method.SIMPLE_METHOD' HEADGOAL o tac o local_simpset_of);

val perm_eq_meth            = simp_meth_setup (perm_simp_tac NO_DEBUG_tac);
val perm_eq_meth_debug      = simp_meth_setup (perm_simp_tac DEBUG_tac);
val perm_full_eq_meth       = simp_meth_setup (perm_full_simp_tac NO_DEBUG_tac);
val perm_full_eq_meth_debug = simp_meth_setup (perm_full_simp_tac DEBUG_tac);
val supports_meth           = simp_meth_setup (supports_tac NO_DEBUG_tac);
val supports_meth_debug     = simp_meth_setup (supports_tac DEBUG_tac);
val finite_gs_meth          = simp_meth_setup (finite_guess_tac NO_DEBUG_tac);
val finite_gs_meth_debug    = simp_meth_setup (finite_guess_tac DEBUG_tac);
val fresh_gs_meth           = simp_meth_setup (fresh_guess_tac NO_DEBUG_tac);
val fresh_gs_meth_debug     = simp_meth_setup (fresh_guess_tac DEBUG_tac);

end



