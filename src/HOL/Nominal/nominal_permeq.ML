(*  Title:      HOL/Nominal/nominal_permeq.ML
    Author:     Christian Urban, TU Muenchen
    Author:     Julien Narboux, TU Muenchen

Methods for simplifying permutations and for analysing equations
involving permutations.
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
  val perm_fun_simproc : simproc
  val perm_app_simproc : simproc

  val perm_simp_tac : Proof.context -> int -> tactic
  val perm_extend_simp_tac : Proof.context -> int -> tactic
  val supports_tac : Proof.context -> int -> tactic
  val finite_guess_tac : Proof.context -> int -> tactic
  val fresh_guess_tac : Proof.context -> int -> tactic

  val perm_simp_meth : (Proof.context -> Proof.method) context_parser
  val perm_simp_meth_debug : (Proof.context -> Proof.method) context_parser
  val perm_extend_simp_meth : (Proof.context -> Proof.method) context_parser
  val perm_extend_simp_meth_debug : (Proof.context -> Proof.method) context_parser
  val supports_meth : (Proof.context -> Proof.method) context_parser
  val supports_meth_debug : (Proof.context -> Proof.method) context_parser
  val finite_guess_meth : (Proof.context -> Proof.method) context_parser
  val finite_guess_meth_debug : (Proof.context -> Proof.method) context_parser
  val fresh_guess_meth : (Proof.context -> Proof.method) context_parser
  val fresh_guess_meth_debug : (Proof.context -> Proof.method) context_parser
end

structure NominalPermeq : NOMINAL_PERMEQ =
struct

(* some lemmas needed below *)
val finite_emptyI = @{thm "finite.emptyI"};
val finite_Un     = @{thm "finite_Un"};
val conj_absorb   = @{thm "conj_absorb"};
val not_false     = @{thm "not_False_eq_True"}
val perm_fun_def  = Simpdata.mk_eq @{thm "Nominal.perm_fun_def"};
val perm_eq_app   = @{thm "Nominal.pt_fun_app_eq"};
val supports_def  = Simpdata.mk_eq @{thm "Nominal.supports_def"};
val fresh_def     = Simpdata.mk_eq @{thm "Nominal.fresh_def"};
val fresh_prod    = @{thm "Nominal.fresh_prod"};
val fresh_unit    = @{thm "Nominal.fresh_unit"};
val supports_rule = @{thm "supports_finite"};
val supp_prod     = @{thm "supp_prod"};
val supp_unit     = @{thm "supp_unit"};
val pt_perm_compose_aux = @{thm "pt_perm_compose_aux"};
val cp1_aux             = @{thm "cp1_aux"};
val perm_aux_fold       = @{thm "perm_aux_fold"};
val supports_fresh_rule = @{thm "supports_fresh"};

(* needed in the process of fully simplifying permutations *)
val strong_congs = [@{thm "if_cong"}]
(* needed to avoid warnings about overwritten congs *)
val weak_congs   = [@{thm "if_weak_cong"}]

(* debugging *)
fun DEBUG ctxt (msg,tac) =
    CHANGED (EVERY [print_tac ctxt ("before "^msg), tac, print_tac ctxt ("after "^msg)]);
fun NO_DEBUG _ (_,tac) = CHANGED tac;


(* simproc that deals with instances of permutations in front *)
(* of applications; just adding this rule to the simplifier   *)
(* would loop; it also needs careful tuning with the simproc  *)
(* for functions to avoid further possibilities for looping   *)
fun perm_app_proc ctxt ct =
  let
    val thy = Proof_Context.theory_of ctxt
    val redex = Thm.term_of ct
    (* the "application" case is only applicable when the head of f is not a *)
    (* constant or when (f x) is a permuation with two or more arguments     *)
    fun applicable_app t =
          (case (strip_comb t) of
              (Const (\<^const_name>\<open>Nominal.perm\<close>,_),ts) => (length ts) >= 2
            | (Const _,_) => false
            | _ => true)
  in
    case redex of
        (* case pi o (f x) == (pi o f) (pi o x)          *)
        (Const(\<^const_name>\<open>Nominal.perm\<close>,
          Type(\<^type_name>\<open>fun\<close>,
            [Type(\<^type_name>\<open>list\<close>, [Type(\<^type_name>\<open>prod\<close>,[Type(n,_),_])]),_])) $ pi $ (f $ x)) =>
            (if (applicable_app f) then
              let
                val name = Long_Name.base_name n
                val at_inst = Global_Theory.get_thm thy ("at_" ^ name ^ "_inst")
                val pt_inst = Global_Theory.get_thm thy ("pt_" ^ name ^ "_inst")
              in SOME ((at_inst RS (pt_inst RS perm_eq_app)) RS eq_reflection) end
            else NONE)
      | _ => NONE
  end

val perm_app_simproc = \<^simproc_setup>\<open>passive perm_app ("Nominal.perm pi x") = \<open>K perm_app_proc\<close>\<close>

(* a simproc that deals with permutation instances in front of functions  *)
fun perm_fun_proc ctxt ct =
   let
     val redex = Thm.term_of ct
     fun applicable_fun t =
       (case (strip_comb t) of
          (Abs _ ,[]) => true
        | (Const (\<^const_name>\<open>Nominal.perm\<close>,_),_) => false
        | (Const _, _) => true
        | _ => false)
   in
     case redex of
       (* case pi o f == (%x. pi o (f ((rev pi)o x))) *)
       (Const(\<^const_name>\<open>Nominal.perm\<close>,_) $ pi $ f)  =>
          (if applicable_fun f then SOME perm_fun_def else NONE)
      | _ => NONE
   end

val perm_fun_simproc = \<^simproc_setup>\<open>passive perm_fun ("Nominal.perm pi x") = \<open>K perm_fun_proc\<close>\<close>

(* function for simplyfying permutations          *)
(* stac contains the simplifiation tactic that is *)
(* applied (see (no_asm) options below            *)
fun perm_simp_gen stac dyn_thms eqvt_thms ctxt i =
    ("general simplification of permutations", fn st => SUBGOAL (fn _ =>
    let
       val ctxt' = ctxt
         addsimps (maps (Proof_Context.get_thms ctxt) dyn_thms @ eqvt_thms)
         |> Simplifier.add_proc perm_fun_simproc
         |> Simplifier.add_proc perm_app_simproc
         |> fold Simplifier.del_cong weak_congs
         |> fold Simplifier.add_cong strong_congs
    in
      stac ctxt' i
    end) i st);

(* general simplification of permutations and permutation that arose from eqvt-problems *)
fun perm_simp stac ctxt =
    let val simps = ["perm_swap","perm_fresh_fresh","perm_bij","perm_pi_simp","swap_simps"]
    in
        perm_simp_gen stac simps [] ctxt
    end;

fun eqvt_simp stac ctxt =
    let val simps = ["perm_swap","perm_fresh_fresh","perm_pi_simp"]
        val eqvts_thms = NominalThmDecls.get_eqvt_thms ctxt;
    in
        perm_simp_gen stac simps eqvts_thms ctxt
    end;


(* main simplification tactics for permutations *)
fun perm_simp_tac_gen_i stac tactical ctxt i = DETERM (tactical ctxt (perm_simp stac ctxt i));
fun eqvt_simp_tac_gen_i stac tactical ctxt i = DETERM (tactical ctxt (eqvt_simp stac ctxt i));

val perm_simp_tac_i          = perm_simp_tac_gen_i simp_tac
val perm_asm_simp_tac_i      = perm_simp_tac_gen_i asm_simp_tac
val perm_full_simp_tac_i     = perm_simp_tac_gen_i full_simp_tac
val perm_asm_lr_simp_tac_i   = perm_simp_tac_gen_i asm_lr_simp_tac
val perm_asm_full_simp_tac_i = perm_simp_tac_gen_i asm_full_simp_tac
val eqvt_asm_full_simp_tac_i = eqvt_simp_tac_gen_i asm_full_simp_tac

(* applies the perm_compose rule such that                             *)
(*   pi o (pi' o lhs) = rhs                                            *)
(* is transformed to                                                   *)
(*  (pi o pi') o (pi' o lhs) = rhs                                     *)
(*                                                                     *)
(* this rule would loop in the simplifier, so some trick is used with  *)
(* generating perm_aux'es for the outermost permutation and then un-   *)
(* folding the definition                                              *)

fun perm_compose_proc ctxt ct =
  (case Thm.term_of ct of
     (Const (\<^const_name>\<open>Nominal.perm\<close>, Type (\<^type_name>\<open>fun\<close>, [Type (\<^type_name>\<open>list\<close>,
       [Type (\<^type_name>\<open>Product_Type.prod\<close>, [T as Type (tname,_),_])]),_])) $ pi1 $ (Const (\<^const_name>\<open>Nominal.perm\<close>,
         Type (\<^type_name>\<open>fun\<close>, [Type (\<^type_name>\<open>list\<close>, [Type (\<^type_name>\<open>Product_Type.prod\<close>, [U as Type (uname,_),_])]),_])) $
          pi2 $ t)) =>
    let
      val thy = Proof_Context.theory_of ctxt
      val tname' = Long_Name.base_name tname
      val uname' = Long_Name.base_name uname
    in
      if pi1 <> pi2 then  (* only apply the composition rule in this case *)
        if T = U then
          SOME (Thm.instantiate'
            [SOME (Thm.global_ctyp_of thy (fastype_of t))]
            [SOME (Thm.global_cterm_of thy pi1), SOME (Thm.global_cterm_of thy pi2), SOME (Thm.global_cterm_of thy t)]
            (mk_meta_eq ([Global_Theory.get_thm thy ("pt_"^tname'^"_inst"),
             Global_Theory.get_thm thy ("at_"^tname'^"_inst")] MRS pt_perm_compose_aux)))
        else
          SOME (Thm.instantiate'
            [SOME (Thm.global_ctyp_of thy (fastype_of t))]
            [SOME (Thm.global_cterm_of thy pi1), SOME (Thm.global_cterm_of thy pi2), SOME (Thm.global_cterm_of thy t)]
            (mk_meta_eq (Global_Theory.get_thm thy ("cp_"^tname'^"_"^uname'^"_inst") RS
             cp1_aux)))
      else NONE
    end
  | _ => NONE);

val perm_compose_simproc =
  \<^simproc_setup>\<open>passive perm_compose ("perm pi1 (perm pi2 t)") = \<open>K perm_compose_proc\<close>\<close>;

fun perm_compose_tac ctxt i =
  ("analysing permutation compositions on the lhs",
   fn st => EVERY
     [resolve_tac ctxt [trans] i,
      asm_full_simp_tac (Simplifier.empty_simpset ctxt |> Simplifier.add_proc perm_compose_simproc) i,
      asm_full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps [perm_aux_fold]) i] st);

fun apply_cong_tac ctxt i = ("application of congruence", cong_tac ctxt i);


(* unfolds the definition of permutations     *)
(* applied to functions such that             *)
(*     pi o f = rhs                           *)
(* is transformed to                          *)
(*     %x. pi o (f ((rev pi) o x)) = rhs      *)
fun unfold_perm_fun_def_tac ctxt i =
    ("unfolding of permutations on functions",
      resolve_tac ctxt [HOLogic.mk_obj_eq perm_fun_def RS trans] i)

(* applies the ext-rule such that      *)
(*                                     *)
(*    f = g   goes to  /\x. f x = g x  *)
fun ext_fun_tac ctxt i =
  ("extensionality expansion of functions", resolve_tac ctxt @{thms ext} i);


(* perm_extend_simp_tac_i is perm_simp plus additional tactics        *)
(* to decide equation that come from support problems             *)
(* since it contains looping rules the "recursion" - depth is set *)
(* to 10 - this seems to be sufficient in most cases              *)
fun perm_extend_simp_tac_i tactical ctxt =
  let fun perm_extend_simp_tac_aux tactical ctxt n =
          if n=0 then K all_tac
          else DETERM o
               (FIRST'
                 [fn i => tactical ctxt ("splitting conjunctions on the rhs", resolve_tac ctxt [conjI] i),
                  fn i => tactical ctxt (perm_simp asm_full_simp_tac ctxt i),
                  fn i => tactical ctxt (perm_compose_tac ctxt i),
                  fn i => tactical ctxt (apply_cong_tac ctxt i),
                  fn i => tactical ctxt (unfold_perm_fun_def_tac ctxt i),
                  fn i => tactical ctxt (ext_fun_tac ctxt i)]
                THEN_ALL_NEW (TRY o (perm_extend_simp_tac_aux tactical ctxt (n-1))))
  in perm_extend_simp_tac_aux tactical ctxt 10 end;


(* tactic that tries to solve "supports"-goals; first it *)
(* unfolds the support definition and strips off the     *)
(* intros, then applies eqvt_simp_tac                    *)
fun supports_tac_i tactical ctxt i =
  let
     val simps        = [supports_def, Thm.symmetric fresh_def, fresh_prod]
  in
      EVERY [tactical ctxt ("unfolding of supports   ", simp_tac (put_simpset HOL_basic_ss ctxt addsimps simps) i),
             tactical ctxt ("stripping of foralls    ", REPEAT_DETERM (resolve_tac ctxt [allI] i)),
             tactical ctxt ("geting rid of the imps  ", resolve_tac ctxt [impI] i),
             tactical ctxt ("eliminating conjuncts   ", REPEAT_DETERM (eresolve_tac ctxt [conjE] i)),
             tactical ctxt ("applying eqvt_simp      ", eqvt_simp_tac_gen_i asm_full_simp_tac tactical ctxt i)]
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

(* FIXME proper SUBGOAL/CSUBGOAL instead of cprems_of etc. *)
fun finite_guess_tac_i tactical ctxt i st =
    let val goal = nth (Thm.cprems_of st) (i - 1)
    in
      case Envir.eta_contract (Logic.strip_assums_concl (Thm.term_of goal)) of
          _ $ (Const (\<^const_name>\<open>finite\<close>, _) $ (Const (\<^const_name>\<open>Nominal.supp\<close>, T) $ x)) =>
          let
            val ps = Logic.strip_params (Thm.term_of goal);
            val Ts = rev (map snd ps);
            val vs = collect_vars 0 x [];
            val s = fold_rev (fn v => fn s =>
                HOLogic.pair_const (fastype_of1 (Ts, v)) (fastype_of1 (Ts, s)) $ v $ s)
              vs HOLogic.unit;
            val s' = fold_rev Term.abs ps
              (Const (\<^const_name>\<open>Nominal.supp\<close>, fastype_of1 (Ts, s) -->
                Term.range_type T) $ s);
            val supports_rule' = Thm.lift_rule goal supports_rule;
            val _ $ (_ $ S $ _) =
              Logic.strip_assums_concl (hd (Thm.prems_of supports_rule'));
            val supports_rule'' =
              infer_instantiate ctxt
                [(#1 (dest_Var (head_of S)), Thm.cterm_of ctxt s')] supports_rule';
            val fin_supp = Proof_Context.get_thms ctxt "fin_supp"
            val ctxt' = ctxt addsimps [supp_prod,supp_unit,finite_Un,finite_emptyI,conj_absorb]@fin_supp
          in
            (tactical ctxt ("guessing of the right supports-set",
                      EVERY [compose_tac ctxt (false, supports_rule'', 2) i,
                             asm_full_simp_tac ctxt' (i+1),
                             supports_tac_i tactical ctxt i])) st
          end
        | _ => Seq.empty
    end
    handle General.Subscript => Seq.empty
(* FIXME proper SUBGOAL/CSUBGOAL instead of cprems_of etc. *)


(* tactic that guesses whether an atom is fresh for an expression  *)
(* it first collects all free variables and tries to show that the *)
(* support of these free variables (op supports) the goal          *)
(* FIXME proper SUBGOAL/CSUBGOAL instead of cprems_of etc. *)
fun fresh_guess_tac_i tactical ctxt i st =
    let
        val goal = nth (Thm.cprems_of st) (i - 1)
        val fin_supp = Proof_Context.get_thms ctxt "fin_supp"
        val fresh_atm = Proof_Context.get_thms ctxt "fresh_atm"
        val ctxt1 = ctxt addsimps [Thm.symmetric fresh_def,fresh_prod,fresh_unit,conj_absorb,not_false]@fresh_atm
        val ctxt2 = ctxt addsimps [supp_prod,supp_unit,finite_Un,finite_emptyI,conj_absorb]@fin_supp
    in
      case Logic.strip_assums_concl (Thm.term_of goal) of
          _ $ (Const (\<^const_name>\<open>Nominal.fresh\<close>, Type ("fun", [T, _])) $ _ $ t) =>
          let
            val ps = Logic.strip_params (Thm.term_of goal);
            val Ts = rev (map snd ps);
            val vs = collect_vars 0 t [];
            val s = fold_rev (fn v => fn s =>
                HOLogic.pair_const (fastype_of1 (Ts, v)) (fastype_of1 (Ts, s)) $ v $ s)
              vs HOLogic.unit;
            val s' =
              fold_rev Term.abs ps
                (Const (\<^const_name>\<open>Nominal.supp\<close>, fastype_of1 (Ts, s) --> HOLogic.mk_setT T) $ s);
            val supports_fresh_rule' = Thm.lift_rule goal supports_fresh_rule;
            val _ $ (_ $ S $ _) =
              Logic.strip_assums_concl (hd (Thm.prems_of supports_fresh_rule'));
            val supports_fresh_rule'' =
              infer_instantiate ctxt
                [(#1 (dest_Var (head_of S)), Thm.cterm_of ctxt s')] supports_fresh_rule';
          in
            (tactical ctxt ("guessing of the right set that supports the goal",
                      (EVERY [compose_tac ctxt (false, supports_fresh_rule'', 3) i,
                             asm_full_simp_tac ctxt1 (i+2),
                             asm_full_simp_tac ctxt2 (i+1),
                             supports_tac_i tactical ctxt i]))) st
          end
          (* when a term-constructor contains more than one binder, it is useful    *)
          (* in nominal_primrecs to try whether the goal can be solved by an hammer *)
        | _ => (tactical ctxt ("if it is not of the form _\<sharp>_, then try the simplifier",
                          (asm_full_simp_tac (put_simpset HOL_ss ctxt addsimps [fresh_prod]@fresh_atm) i))) st
    end
    handle General.Subscript => Seq.empty;
(* FIXME proper SUBGOAL/CSUBGOAL instead of cprems_of etc. *)

val eqvt_simp_tac        = eqvt_asm_full_simp_tac_i NO_DEBUG;

val perm_simp_tac        = perm_asm_full_simp_tac_i NO_DEBUG;
val perm_extend_simp_tac = perm_extend_simp_tac_i NO_DEBUG;
val supports_tac         = supports_tac_i NO_DEBUG;
val finite_guess_tac     = finite_guess_tac_i NO_DEBUG;
val fresh_guess_tac      = fresh_guess_tac_i NO_DEBUG;

val dperm_simp_tac        = perm_asm_full_simp_tac_i DEBUG;
val dperm_extend_simp_tac = perm_extend_simp_tac_i DEBUG;
val dsupports_tac         = supports_tac_i DEBUG;
val dfinite_guess_tac     = finite_guess_tac_i DEBUG;
val dfresh_guess_tac      = fresh_guess_tac_i DEBUG;

(* Code opied from the Simplifer for setting up the perm_simp method   *)
(* behaves nearly identical to the simp-method, for example can handle *)
(* options like (no_asm) etc.                                          *)
val no_asmN = "no_asm";
val no_asm_useN = "no_asm_use";
val no_asm_simpN = "no_asm_simp";
val asm_lrN = "asm_lr";

val perm_simp_options =
 (Args.parens (Args.$$$ no_asmN) >> K (perm_simp_tac_i NO_DEBUG) ||
  Args.parens (Args.$$$ no_asm_simpN) >> K (perm_asm_simp_tac_i NO_DEBUG) ||
  Args.parens (Args.$$$ no_asm_useN) >> K (perm_full_simp_tac_i NO_DEBUG) ||
  Args.parens (Args.$$$ asm_lrN) >> K (perm_asm_lr_simp_tac_i NO_DEBUG) ||
  Scan.succeed (perm_asm_full_simp_tac_i NO_DEBUG));

val perm_simp_meth =
  Scan.lift perm_simp_options --| Method.sections (Simplifier.simp_modifiers') >>
  (fn tac => fn ctxt => SIMPLE_METHOD' (CHANGED_PROP o tac ctxt));

(* setup so that the simpset is used which is active at the moment when the tactic is called *)
fun local_simp_meth_setup tac =
  Method.sections (Simplifier.simp_modifiers' @ Splitter.split_modifiers) >>
  (K (SIMPLE_METHOD' o tac));

(* uses HOL_basic_ss only and fails if the tactic does not solve the subgoal *)

fun basic_simp_meth_setup debug tac =
  Scan.depend (fn context => Scan.succeed (Simplifier.map_simpset (put_simpset HOL_basic_ss) context, ())) --
  Method.sections (Simplifier.simp_modifiers' @ Splitter.split_modifiers) >>
  (K (SIMPLE_METHOD' o (if debug then tac else SOLVED' o tac)));

val perm_simp_meth_debug        = local_simp_meth_setup dperm_simp_tac;
val perm_extend_simp_meth       = local_simp_meth_setup perm_extend_simp_tac;
val perm_extend_simp_meth_debug = local_simp_meth_setup dperm_extend_simp_tac;
val supports_meth               = local_simp_meth_setup supports_tac;
val supports_meth_debug         = local_simp_meth_setup dsupports_tac;

val finite_guess_meth         = basic_simp_meth_setup false finite_guess_tac;
val finite_guess_meth_debug   = basic_simp_meth_setup true  dfinite_guess_tac;
val fresh_guess_meth          = basic_simp_meth_setup false fresh_guess_tac;
val fresh_guess_meth_debug    = basic_simp_meth_setup true  dfresh_guess_tac;

end
