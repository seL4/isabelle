(*  Title:      HOL/Nominal/nominal_permeq.ML
    ID:         $Id$
    Authors:    Christian Urban, Julien Narboux, TU Muenchen

Methods for simplifying permutations and
for analysing equations involving permutations.
*)

(*
FIXMES:

 - allow the user to give an explicit set S in the
   fresh_guess tactic which is then verified

 - the perm_compose tactic does not do an "outermost
   rewriting" and can therefore not deal with goals
   like

      [(a,b)] o pi1 o pi2 = ....

   rather it tries to permute pi1 over pi2, which 
   results in a failure when used with the 
   perm_(full)_simp tactics

*)


signature NOMINAL_PERMEQ =
sig
  val perm_simp_tac : simpset -> int -> tactic
  val perm_full_simp_tac : simpset -> int -> tactic
  val supports_tac : simpset -> int -> tactic
  val finite_guess_tac : simpset -> int -> tactic
  val fresh_guess_tac : simpset -> int -> tactic

  val perm_simp_meth : Method.src -> Proof.context -> Proof.method
  val perm_simp_meth_debug : Method.src -> Proof.context -> Proof.method
  val perm_full_simp_meth : Method.src -> Proof.context -> Proof.method
  val perm_full_simp_meth_debug : Method.src -> Proof.context -> Proof.method
  val supports_meth : Method.src -> Proof.context -> Proof.method
  val supports_meth_debug : Method.src -> Proof.context -> Proof.method
  val finite_guess_meth : Method.src -> Proof.context -> Proof.method
  val finite_guess_meth_debug : Method.src -> Proof.context -> Proof.method
  val fresh_guess_meth : Method.src -> Proof.context -> Proof.method
  val fresh_guess_meth_debug : Method.src -> Proof.context -> Proof.method
end

structure NominalPermeq : NOMINAL_PERMEQ =
struct

(* some lemmas needed below *)
val finite_emptyI = @{thm "finite.emptyI"};
val finite_Un     = @{thm "finite_Un"};
val conj_absorb   = @{thm "conj_absorb"};
val not_false     = @{thm "not_False_eq_True"}
val perm_fun_def  = @{thm "Nominal.perm_fun_def"};
val perm_eq_app   = @{thm "Nominal.pt_fun_app_eq"};
val supports_def  = @{thm "Nominal.supports_def"};
val fresh_def     = @{thm "Nominal.fresh_def"};
val fresh_prod    = @{thm "Nominal.fresh_prod"};
val fresh_unit    = @{thm "Nominal.fresh_unit"};
val supports_rule = @{thm "supports_finite"};
val supp_prod     = @{thm "supp_prod"};
val supp_unit     = @{thm "supp_unit"};
val pt_perm_compose_aux = @{thm "pt_perm_compose_aux"};
val cp1_aux             = @{thm "cp1_aux"};
val perm_aux_fold       = @{thm "perm_aux_fold"}; 
val supports_fresh_rule = @{thm "supports_fresh"};

(* pulls out dynamically a thm via the proof state *)
fun dynamic_thms st name = PureThy.get_thms (theory_of_thm st) (Name name);
fun dynamic_thm  st name = PureThy.get_thm  (theory_of_thm st) (Name name);


(* needed in the process of fully simplifying permutations *)
val strong_congs = [@{thm "if_cong"}]
(* needed to avoid warnings about overwritten congs *)
val weak_congs   = [@{thm "if_weak_cong"}]

(* FIXME comment *)
(* a tactical which fails if the tactic taken as an argument generates does not solve the sub goal i *)
fun SOLVEI t = t THEN_ALL_NEW (fn i => no_tac);

(* debugging *)
fun DEBUG_tac (msg,tac) = 
    CHANGED (EVERY [print_tac ("before "^msg), tac, print_tac ("after "^msg)]); 
fun NO_DEBUG_tac (_,tac) = CHANGED tac; 


(* simproc that deals with instances of permutations in front *)
(* of applications; just adding this rule to the simplifier   *)
(* would loop; it also needs careful tuning with the simproc  *)
(* for functions to avoid further possibilities for looping   *)
fun perm_simproc_app st sg ss redex =
  let 
    (* the "application" case is only applicable when the head of f is not a *)
    (* constant or when (f x) is a permuation with two or more arguments     *)
    fun applicable_app t = 
          (case (strip_comb t) of
	      (Const ("Nominal.perm",_),ts) => (length ts) >= 2
            | (Const _,_) => false
            | _ => true)
  in
    case redex of 
        (* case pi o (f x) == (pi o f) (pi o x)          *)
        (Const("Nominal.perm",
          Type("fun",[Type("List.list",[Type("*",[Type(n,_),_])]),_])) $ pi $ (f $ x)) => 
            (if (applicable_app f) then
              let
                val name = Sign.base_name n
                val at_inst     = dynamic_thm st ("at_"^name^"_inst")
                val pt_inst     = dynamic_thm st ("pt_"^name^"_inst")  
              in SOME ((at_inst RS (pt_inst RS perm_eq_app)) RS eq_reflection) end
            else NONE)
      | _ => NONE
  end

(* a simproc that deals with permutation instances in front of functions  *)
fun perm_simproc_fun st sg ss redex = 
   let 
     fun applicable_fun t =
       (case (strip_comb t) of
          (Abs _ ,[]) => true
	| (Const ("Nominal.perm",_),_) => false
        | (Const _, _) => true
	| _ => false)
   in
     case redex of 
       (* case pi o f == (%x. pi o (f ((rev pi)o x))) *)     
       (Const("Nominal.perm",_) $ pi $ f)  => 
          (if (applicable_fun f) then SOME (perm_fun_def) else NONE)
      | _ => NONE
   end

(* function for simplyfying permutations *)
fun perm_simp_gen dyn_thms f ss i = 
    ("general simplification of permutations", fn st =>
    let

       val perm_sp_fun = Simplifier.simproc (theory_of_thm st) "perm_simproc_fun" 
	                 ["Nominal.perm pi x"] (perm_simproc_fun st);

       val perm_sp_app = Simplifier.simproc (theory_of_thm st) "perm_simproc_app" 
	                 ["Nominal.perm pi x"] (perm_simproc_app st);

       val ss' = ss addsimps ((List.concat (map (dynamic_thms st) dyn_thms))@(f st))
                    delcongs weak_congs
                    addcongs strong_congs
                    addsimprocs [perm_sp_fun, perm_sp_app]
    in
      asm_full_simp_tac ss' i st
    end);

(* general simplification of permutations and permutation that arose from eqvt-problems *)
val perm_simp = 
    let val simps = ["perm_swap","perm_fresh_fresh","perm_bij","perm_pi_simp","swap_simps"]
    in 
	perm_simp_gen simps (fn st => [])
    end;

val eqvt_simp = 
    let val simps = ["perm_swap","perm_fresh_fresh","perm_pi_simp"]
	fun eqvts_thms st = NominalThmDecls.get_eqvt_thms (theory_of_thm st);
    in 
	perm_simp_gen simps eqvts_thms
    end;

(* FIXME removes the name lookup for these theorems use an ml value instead *)

(* main simplification tactics for permutations *)
(* FIXME: perm_simp_tac should simplify more permutations *)
fun perm_simp_tac tactical ss i = DETERM (tactical (perm_simp ss i));
fun eqvt_simp_tac tactical ss i = DETERM (tactical (eqvt_simp ss i)); 


(* applies the perm_compose rule such that                             *)
(*   pi o (pi' o lhs) = rhs                                            *)
(* is transformed to                                                   *) 
(*  (pi o pi') o (pi' o lhs) = rhs                                     *)
(*                                                                     *)
(* this rule would loop in the simplifier, so some trick is used with  *)
(* generating perm_aux'es for the outermost permutation and then un-   *)
(* folding the definition                                              *)
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

      val ss' = Simplifier.theory_context (the_context ()) empty_ss (* FIXME: get rid of the_context *)	  

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
(*     pi o f = rhs                           *)  
(* is transformed to                          *)
(*     %x. pi o (f ((rev pi) o x)) = rhs      *)
fun unfold_perm_fun_def_tac i =
    ("unfolding of permutations on functions", 
      rtac (perm_fun_def RS meta_eq_to_obj_eq RS trans) i)

(* applies the ext-rule such that      *)
(*                                     *)
(*    f = g   goes to  /\x. f x = g x  *)
fun ext_fun_tac i = ("extensionality expansion of functions", rtac ext i);


(* perm_full_simp_tac is perm_simp plus additional tactics        *)
(* to decide equation that come from support problems             *)
(* since it contains looping rules the "recursion" - depth is set *)
(* to 10 - this seems to be sufficient in most cases              *)
fun perm_full_simp_tac tactical ss =
  let fun perm_full_simp_tac_aux tactical ss n = 
	  if n=0 then K all_tac
	  else DETERM o 
	       (FIRST'[fn i => tactical ("splitting conjunctions on the rhs", rtac conjI i),
                       fn i => tactical (perm_simp ss i),
		       fn i => tactical (perm_compose_tac ss i),
		       fn i => tactical (apply_cong_tac i), 
                       fn i => tactical (unfold_perm_fun_def_tac i),
                       fn i => tactical (ext_fun_tac i)]
		      THEN_ALL_NEW (TRY o (perm_full_simp_tac_aux tactical ss (n-1))))
  in perm_full_simp_tac_aux tactical ss 10 end;


(* tactic that tries to solve "supports"-goals; first it *)
(* unfolds the support definition and strips off the     *)
(* intros, then applies eqvt_simp_tac                    *)
fun supports_tac tactical ss i =
  let 
     val simps        = [supports_def,symmetric fresh_def,fresh_prod]
  in
      EVERY [tactical ("unfolding of supports   ", simp_tac (HOL_basic_ss addsimps simps) i),
             tactical ("stripping of foralls    ", REPEAT_DETERM (rtac allI i)),
             tactical ("geting rid of the imps  ", rtac impI i),
             tactical ("eliminating conjuncts   ", REPEAT_DETERM (etac  conjE i)),
             tactical ("applying eqvt_simp      ", eqvt_simp_tac tactical ss i )]
  end;


(* tactic that guesses the finite-support of a goal        *)
(* it first collects all free variables and tries to show  *)
(* that the support of these free variables (op supports)  *)
(* the goal                                                *)
fun collect_vars i (Bound j) vs = if j < i then vs else insert (op =) (Bound (j - i)) vs
  | collect_vars i (v as Free _) vs = insert (op =) v vs
  | collect_vars i (v as Var _) vs = insert (op =) v vs
  | collect_vars i (Const _) vs = vs
  | collect_vars i (Abs (_, _, t)) vs = collect_vars (i+1) t vs
  | collect_vars i (t $ u) vs = collect_vars i u (collect_vars i t vs);

fun finite_guess_tac tactical ss i st =
    let val goal = List.nth(cprems_of st, i-1)
    in
      case Logic.strip_assums_concl (term_of goal) of
          _ $ (Const ("Finite_Set.finite", _) $ (Const ("Nominal.supp", T) $ x)) =>
          let
            val cert = Thm.cterm_of (Thm.theory_of_thm st);
            val ps = Logic.strip_params (term_of goal);
            val Ts = rev (map snd ps);
            val vs = collect_vars 0 x [];
            val s = Library.foldr (fn (v, s) =>
                HOLogic.pair_const (fastype_of1 (Ts, v)) (fastype_of1 (Ts, s)) $ v $ s)
              (vs, HOLogic.unit);
            val s' = list_abs (ps,
              Const ("Nominal.supp", fastype_of1 (Ts, s) --> body_type T) $ s);
            val supports_rule' = Thm.lift_rule goal supports_rule;
            val _ $ (_ $ S $ _) =
              Logic.strip_assums_concl (hd (prems_of supports_rule'));
            val supports_rule'' = Drule.cterm_instantiate
              [(cert (head_of S), cert s')] supports_rule'
            val fin_supp = dynamic_thms st ("fin_supp")
            val ss' = ss addsimps [supp_prod,supp_unit,finite_Un,finite_emptyI,conj_absorb]@fin_supp
          in
            (tactical ("guessing of the right supports-set",
                      EVERY [compose_tac (false, supports_rule'', 2) i,
                             asm_full_simp_tac ss' (i+1),
                             supports_tac tactical ss i])) st
          end
        | _ => Seq.empty
    end
    handle Subscript => Seq.empty


(* tactic that guesses whether an atom is fresh for an expression  *)
(* it first collects all free variables and tries to show that the *) 
(* support of these free variables (op supports) the goal          *)
fun fresh_guess_tac tactical ss i st =
    let 
	val goal = List.nth(cprems_of st, i-1)
        val fin_supp = dynamic_thms st ("fin_supp")
        val fresh_atm = dynamic_thms st ("fresh_atm")
	val ss1 = ss addsimps [symmetric fresh_def,fresh_prod,fresh_unit,conj_absorb,not_false]@fresh_atm
        val ss2 = ss addsimps [supp_prod,supp_unit,finite_Un,finite_emptyI,conj_absorb]@fin_supp
    in
      case Logic.strip_assums_concl (term_of goal) of
          _ $ (Const ("Nominal.fresh", Type ("fun", [T, _])) $ _ $ t) => 
          let
            val cert = Thm.cterm_of (Thm.theory_of_thm st);
            val ps = Logic.strip_params (term_of goal);
            val Ts = rev (map snd ps);
            val vs = collect_vars 0 t [];
            val s = Library.foldr (fn (v, s) =>
                HOLogic.pair_const (fastype_of1 (Ts, v)) (fastype_of1 (Ts, s)) $ v $ s)
              (vs, HOLogic.unit);
            val s' = list_abs (ps,
              Const ("Nominal.supp", fastype_of1 (Ts, s) --> (HOLogic.mk_setT T)) $ s);
            val supports_fresh_rule' = Thm.lift_rule goal supports_fresh_rule;
            val _ $ (_ $ S $ _) =
              Logic.strip_assums_concl (hd (prems_of supports_fresh_rule'));
            val supports_fresh_rule'' = Drule.cterm_instantiate
              [(cert (head_of S), cert s')] supports_fresh_rule'
          in
            (tactical ("guessing of the right set that supports the goal", 
                      (EVERY [compose_tac (false, supports_fresh_rule'', 3) i,
                             asm_full_simp_tac ss1 (i+2),
                             asm_full_simp_tac ss2 (i+1), 
                             supports_tac tactical ss i]))) st
          end
          (* when a term-constructor contains more than one binder, it is useful    *) 
          (* in nominal_primrecs to try whether the goal can be solved by an hammer *)
        | _ => (tactical ("if it is not of the form _\<sharp>_, then try the simplifier",   
                          (asm_full_simp_tac (HOL_ss addsimps [fresh_prod]@fresh_atm) i))) st
    end
    handle Subscript => Seq.empty;

(* setup so that the simpset is used which is active at the moment when the tactic is called *)
fun local_simp_meth_setup tac =
  Method.only_sectioned_args (Simplifier.simp_modifiers' @ Splitter.split_modifiers)
  (Method.SIMPLE_METHOD' o tac o local_simpset_of) ;

(* uses HOL_basic_ss only and fails if the tactic does not solve the subgoal *)

fun basic_simp_meth_setup debug tac =
  Method.sectioned_args 
   (fn (ctxt,l) => ((),((Simplifier.map_ss (fn _ => HOL_basic_ss) ctxt),l)))
   (Simplifier.simp_modifiers' @ Splitter.split_modifiers)
   (fn _ => Method.SIMPLE_METHOD' o (fn ss => if debug then (tac ss) else SOLVEI (tac ss)) o local_simpset_of);


val perm_simp_meth            = local_simp_meth_setup (perm_simp_tac NO_DEBUG_tac);
val perm_simp_meth_debug      = local_simp_meth_setup (perm_simp_tac DEBUG_tac);
val perm_full_simp_meth       = local_simp_meth_setup (perm_full_simp_tac NO_DEBUG_tac);
val perm_full_simp_meth_debug = local_simp_meth_setup (perm_full_simp_tac DEBUG_tac);
val supports_meth             = local_simp_meth_setup (supports_tac NO_DEBUG_tac);
val supports_meth_debug       = local_simp_meth_setup (supports_tac DEBUG_tac);
val finite_guess_meth         = basic_simp_meth_setup false (finite_guess_tac NO_DEBUG_tac);
val finite_guess_meth_debug   = basic_simp_meth_setup true (finite_guess_tac DEBUG_tac);
val fresh_guess_meth          = basic_simp_meth_setup false (fresh_guess_tac NO_DEBUG_tac);
val fresh_guess_meth_debug    = basic_simp_meth_setup true (fresh_guess_tac DEBUG_tac);

val perm_simp_tac = perm_simp_tac NO_DEBUG_tac;
val perm_full_simp_tac = perm_full_simp_tac NO_DEBUG_tac;
val supports_tac = supports_tac NO_DEBUG_tac;
val finite_guess_tac = finite_guess_tac NO_DEBUG_tac;
val fresh_guess_tac = fresh_guess_tac NO_DEBUG_tac;

end
