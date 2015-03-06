(*  Title:      HOL/Tools/Function/partial_function.ML
    Author:     Alexander Krauss, TU Muenchen

Partial function definitions based on least fixed points in ccpos.
*)

signature PARTIAL_FUNCTION =
sig
  val init: string -> term -> term -> thm -> thm -> thm option -> declaration

  val mono_tac: Proof.context -> int -> tactic

  val add_partial_function: string -> (binding * typ option * mixfix) list ->
    Attrib.binding * term -> local_theory -> local_theory

  val add_partial_function_cmd: string -> (binding * string option * mixfix) list ->
    Attrib.binding * string -> local_theory -> local_theory
end;


structure Partial_Function: PARTIAL_FUNCTION =
struct

(*** Context Data ***)

datatype setup_data = Setup_Data of 
 {fixp: term,
  mono: term,
  fixp_eq: thm,
  fixp_induct: thm,
  fixp_induct_user: thm option};

structure Modes = Generic_Data
(
  type T = setup_data Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data = Symtab.merge (K true) data;
)

fun init mode fixp mono fixp_eq fixp_induct fixp_induct_user phi =
  let
    val term = Morphism.term phi;
    val thm = Morphism.thm phi;
    val data' = Setup_Data 
      {fixp=term fixp, mono=term mono, fixp_eq=thm fixp_eq,
       fixp_induct=thm fixp_induct, fixp_induct_user=Option.map thm fixp_induct_user};
  in
    Modes.map (Symtab.update (mode, data'))
  end

val known_modes = Symtab.keys o Modes.get o Context.Proof;
val lookup_mode = Symtab.lookup o Modes.get o Context.Proof;


(*** Automated monotonicity proofs ***)

fun strip_cases ctac = ctac #> Seq.map snd;

(*rewrite conclusion with k-th assumtion*)
fun rewrite_with_asm_tac ctxt k =
  Subgoal.FOCUS (fn {context = ctxt', prems, ...} =>
    Local_Defs.unfold_tac ctxt' [nth prems k]) ctxt;

fun dest_case ctxt t =
  case strip_comb t of
    (Const (case_comb, _), args) =>
      (case Ctr_Sugar.ctr_sugar_of_case ctxt case_comb of
         NONE => NONE
       | SOME {case_thms, ...} =>
           let
             val lhs = Thm.prop_of (hd case_thms)
               |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst;
             val arity = length (snd (strip_comb lhs));
             val conv = funpow (length args - arity) Conv.fun_conv
               (Conv.rewrs_conv (map mk_meta_eq case_thms));
           in
             SOME (nth args (arity - 1), conv)
           end)
  | _ => NONE;

(*split on case expressions*)
val split_cases_tac = Subgoal.FOCUS_PARAMS (fn {context = ctxt, ...} =>
  SUBGOAL (fn (t, i) => case t of
    _ $ (_ $ Abs (_, _, body)) =>
      (case dest_case ctxt body of
         NONE => no_tac
       | SOME (arg, conv) =>
           let open Conv in
              if Term.is_open arg then no_tac
              else ((DETERM o strip_cases o Induct.cases_tac ctxt false [[SOME arg]] NONE [])
                THEN_ALL_NEW (rewrite_with_asm_tac ctxt 0)
                THEN_ALL_NEW eresolve_tac ctxt @{thms thin_rl}
                THEN_ALL_NEW (CONVERSION
                  (params_conv ~1 (fn ctxt' =>
                    arg_conv (arg_conv (abs_conv (K conv) ctxt'))) ctxt))) i
           end)
  | _ => no_tac) 1);

(*monotonicity proof: apply rules + split case expressions*)
fun mono_tac ctxt =
  K (Local_Defs.unfold_tac ctxt [@{thm curry_def}])
  THEN' (TRY o REPEAT_ALL_NEW
   (resolve_tac ctxt (rev (Named_Theorems.get ctxt @{named_theorems partial_function_mono}))
     ORELSE' split_cases_tac ctxt));


(*** Auxiliary functions ***)

(*positional instantiation with computed type substitution.
  internal version of  attribute "[of s t u]".*)
fun cterm_instantiate' cts thm =
  let
    val thy = Thm.theory_of_thm thm;
    val vs = rev (Term.add_vars (Thm.prop_of thm) [])
      |> map (Thm.global_cterm_of thy o Var);
  in
    cterm_instantiate (zip_options vs cts) thm
  end;

(*Returns t $ u, but instantiates the type of t to make the
application type correct*)
fun apply_inst ctxt t u =
  let
    val thy = Proof_Context.theory_of ctxt;
    val T = domain_type (fastype_of t);
    val T' = fastype_of u;
    val subst = Sign.typ_match thy (T, T') Vartab.empty
      handle Type.TYPE_MATCH => raise TYPE ("apply_inst", [T, T'], [t, u])
  in
    map_types (Envir.norm_type subst) t $ u
  end;

fun head_conv cv ct =
  if can Thm.dest_comb ct then Conv.fun_conv (head_conv cv) ct else cv ct;


(*** currying transformation ***)

fun curry_const (A, B, C) =
  Const (@{const_name Product_Type.curry},
    [HOLogic.mk_prodT (A, B) --> C, A, B] ---> C);

fun mk_curry f =
  case fastype_of f of
    Type ("fun", [Type (_, [S, T]), U]) =>
      curry_const (S, T, U) $ f
  | T => raise TYPE ("mk_curry", [T], [f]);

(* iterated versions. Nonstandard left-nested tuples arise naturally
from "split o split o split"*)
fun curry_n arity = funpow (arity - 1) mk_curry;
fun uncurry_n arity = funpow (arity - 1) HOLogic.mk_split;

val curry_uncurry_ss =
  simpset_of (put_simpset HOL_basic_ss @{context}
    addsimps [@{thm Product_Type.curry_split}, @{thm Product_Type.split_curry}])

val split_conv_ss =
  simpset_of (put_simpset HOL_basic_ss @{context}
    addsimps [@{thm Product_Type.split_conv}]);

val curry_K_ss =
  simpset_of (put_simpset HOL_basic_ss @{context}
    addsimps [@{thm Product_Type.curry_K}]);

(* instantiate generic fixpoint induction and eliminate the canonical assumptions;
  curry induction predicate *)
fun specialize_fixp_induct ctxt args fT fT_uc F curry uncurry mono_thm f_def rule =
  let
    val cert = Thm.cterm_of ctxt
    val ([P], ctxt') = Variable.variant_fixes ["P"] ctxt
    val P_inst = Abs ("f", fT_uc, Free (P, fT --> HOLogic.boolT) $ (curry $ Bound 0))
  in 
    (* FIXME ctxt vs. ctxt' (!?) *)
    rule
    |> cterm_instantiate' [SOME (cert uncurry), NONE, SOME (cert curry), NONE, SOME (cert P_inst)]
    |> Tactic.rule_by_tactic ctxt
      (Simplifier.simp_tac (put_simpset curry_uncurry_ss ctxt) 3 (* discharge U (C f) = f *)
       THEN Simplifier.simp_tac (put_simpset curry_K_ss ctxt) 4 (* simplify bot case *)
       THEN Simplifier.full_simp_tac (put_simpset curry_uncurry_ss ctxt) 5) (* simplify induction step *)
    |> (fn thm => thm OF [mono_thm, f_def])
    |> Conv.fconv_rule (Conv.concl_conv ~1    (* simplify conclusion *)
         (Raw_Simplifier.rewrite ctxt false [mk_meta_eq @{thm Product_Type.curry_split}]))
    |> singleton (Variable.export ctxt' ctxt)
  end

fun mk_curried_induct args ctxt inst_rule =
  let
    val cert = Thm.cterm_of ctxt
    val ([P], ctxt') = Variable.variant_fixes ["P"] ctxt

    val split_paired_all_conv =
      Conv.every_conv (replicate (length args - 1) (Conv.rewr_conv @{thm split_paired_all}))

    val split_params_conv = 
      Conv.params_conv ~1 (fn ctxt' =>
        Conv.implies_conv split_paired_all_conv Conv.all_conv)

    val (P_var, x_var) =
       Thm.prop_of inst_rule |> Logic.strip_imp_concl |> HOLogic.dest_Trueprop
      |> strip_comb |> apsnd hd
    val P_rangeT = range_type (snd (Term.dest_Var P_var))
    val PT = map (snd o dest_Free) args ---> P_rangeT
    val x_inst = cert (foldl1 HOLogic.mk_prod args)
    val P_inst = cert (uncurry_n (length args) (Free (P, PT)))

    val inst_rule' = inst_rule
      |> Tactic.rule_by_tactic ctxt
        (Simplifier.simp_tac (put_simpset curry_uncurry_ss ctxt) 4
         THEN Simplifier.simp_tac (put_simpset curry_uncurry_ss ctxt) 3
         THEN CONVERSION (split_params_conv ctxt
           then_conv (Conv.forall_conv (K split_paired_all_conv) ctxt)) 3)
      |> Thm.instantiate ([], [(cert P_var, P_inst), (cert x_var, x_inst)]) 
      |> Simplifier.full_simplify (put_simpset split_conv_ss ctxt)
      |> singleton (Variable.export ctxt' ctxt)
  in
    inst_rule'
  end;
    

(*** partial_function definition ***)

fun gen_add_partial_function prep mode fixes_raw eqn_raw lthy =
  let
    val setup_data = the (lookup_mode lthy mode)
      handle Option.Option => error (cat_lines ["Unknown mode " ^ quote mode ^ ".",
        "Known modes are " ^ commas_quote (known_modes lthy) ^ "."]);
    val Setup_Data {fixp, mono, fixp_eq, fixp_induct, fixp_induct_user} = setup_data;

    val ((fixes, [(eq_abinding, eqn)]), _) = prep fixes_raw [eqn_raw] lthy;
    val ((_, plain_eqn), args_ctxt) = Variable.focus eqn lthy;

    val ((f_binding, fT), mixfix) = the_single fixes;
    val fname = Binding.name_of f_binding;

    val cert = Thm.cterm_of lthy;
    val (lhs, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop plain_eqn);
    val (head, args) = strip_comb lhs;
    val argnames = map (fst o dest_Free) args;
    val F = fold_rev lambda (head :: args) rhs;

    val arity = length args;
    val (aTs, bTs) = chop arity (binder_types fT);

    val tupleT = foldl1 HOLogic.mk_prodT aTs;
    val fT_uc = tupleT :: bTs ---> body_type fT;
    val f_uc = Var ((fname, 0), fT_uc);
    val x_uc = Var (("x", 0), tupleT);
    val uncurry = lambda head (uncurry_n arity head);
    val curry = lambda f_uc (curry_n arity f_uc);

    val F_uc =
      lambda f_uc (uncurry_n arity (F $ curry_n arity f_uc));

    val mono_goal = apply_inst lthy mono (lambda f_uc (F_uc $ f_uc $ x_uc))
      |> HOLogic.mk_Trueprop
      |> Logic.all x_uc;

    val mono_thm = Goal.prove_internal lthy [] (cert mono_goal)
        (K (mono_tac lthy 1))
    val inst_mono_thm = Thm.forall_elim (cert x_uc) mono_thm

    val f_def_rhs = curry_n arity (apply_inst lthy fixp F_uc);
    val f_def_binding = Binding.conceal (Binding.name (Thm.def_name fname));
    val ((f, (_, f_def)), lthy') = Local_Theory.define
      ((f_binding, mixfix), ((f_def_binding, []), f_def_rhs)) lthy;

    val eqn = HOLogic.mk_eq (list_comb (f, args),
        Term.betapplys (F, f :: args))
      |> HOLogic.mk_Trueprop;

    val unfold =
      (cterm_instantiate' (map (SOME o cert) [uncurry, F, curry]) fixp_eq
        OF [inst_mono_thm, f_def])
      |> Tactic.rule_by_tactic lthy' (Simplifier.simp_tac (put_simpset curry_uncurry_ss lthy') 1);

    val specialized_fixp_induct = 
      specialize_fixp_induct lthy' args fT fT_uc F curry uncurry inst_mono_thm f_def fixp_induct
      |> Drule.rename_bvars' (map SOME (fname :: fname :: argnames));

    val mk_raw_induct =
      cterm_instantiate' [SOME (cert uncurry), NONE, SOME (cert curry)]
      #> mk_curried_induct args args_ctxt
      #> singleton (Variable.export args_ctxt lthy')
      #> (fn thm => cterm_instantiate' [SOME (cert F)] thm OF [inst_mono_thm, f_def])
      #> Drule.rename_bvars' (map SOME (fname :: argnames @ argnames))

    val raw_induct = Option.map mk_raw_induct fixp_induct_user
    val rec_rule = let open Conv in
      Goal.prove lthy' (map (fst o dest_Free) args) [] eqn (fn _ =>
        CONVERSION ((arg_conv o arg1_conv o head_conv o rewr_conv) (mk_meta_eq unfold)) 1
        THEN resolve_tac lthy' @{thms refl} 1) end;
  in
    lthy'
    |> Local_Theory.note (eq_abinding, [rec_rule])
    |-> (fn (_, rec') =>
      Spec_Rules.add Spec_Rules.Equational ([f], rec')
      #> Local_Theory.note ((Binding.qualify true fname (Binding.name "simps"), []), rec') #> snd)
    |> (Local_Theory.note ((Binding.qualify true fname (Binding.name "mono"), []), [mono_thm]) #> snd) 
    |> (case raw_induct of NONE => I | SOME thm =>
         Local_Theory.note ((Binding.qualify true fname (Binding.name "raw_induct"), []), [thm]) #> snd)
    |> (Local_Theory.note ((Binding.qualify true fname (Binding.name "fixp_induct"), []), [specialized_fixp_induct]) #> snd) 
  end;

val add_partial_function = gen_add_partial_function Specification.check_spec;
val add_partial_function_cmd = gen_add_partial_function Specification.read_spec;

val mode = @{keyword "("} |-- Parse.xname --| @{keyword ")"};

val _ =
  Outer_Syntax.local_theory @{command_spec "partial_function"} "define partial function"
    ((mode -- (Parse.fixes -- (Parse.where_ |-- Parse_Spec.spec)))
      >> (fn (mode, (fixes, spec)) => add_partial_function_cmd mode fixes spec));

end
