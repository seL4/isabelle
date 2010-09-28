(*  Title:      HOL/Tools/Predicate_Compile/predicate_compile_core.ML
    Author:     Lukas Bulwahn, TU Muenchen

A compiler from predicates specified by intro/elim rules to equations.
*)

signature PREDICATE_COMPILE_CORE =
sig
  type mode = Predicate_Compile_Aux.mode
  type options = Predicate_Compile_Aux.options
  type compilation = Predicate_Compile_Aux.compilation
  type compilation_funs = Predicate_Compile_Aux.compilation_funs
  
  val setup : theory -> theory
  val code_pred : options -> string -> Proof.context -> Proof.state
  val code_pred_cmd : options -> string -> Proof.context -> Proof.state
  val values_cmd : string list -> mode option list option
    -> ((string option * bool) * (compilation * int list)) -> int -> string -> Toplevel.state -> unit
  val register_predicate : (string * thm list * thm) -> theory -> theory
  val register_intros : string * thm list -> theory -> theory
  val is_registered : Proof.context -> string -> bool
  val function_name_of : compilation -> Proof.context -> string -> mode -> string
  val predfun_intro_of: Proof.context -> string -> mode -> thm
  val predfun_elim_of: Proof.context -> string -> mode -> thm
  val all_preds_of : Proof.context -> string list
  val modes_of: compilation -> Proof.context -> string -> mode list
  val all_modes_of : compilation -> Proof.context -> (string * mode list) list
  val all_random_modes_of : Proof.context -> (string * mode list) list
  val intros_of : Proof.context -> string -> thm list
  val intros_graph_of : Proof.context -> thm list Graph.T
  val add_intro : string option * thm -> theory -> theory
  val set_elim : thm -> theory -> theory
  val register_alternative_function : string -> mode -> string -> theory -> theory
  val alternative_compilation_of_global : theory -> string -> mode ->
    (compilation_funs -> typ -> term) option
  val alternative_compilation_of : Proof.context -> string -> mode ->
    (compilation_funs -> typ -> term) option
  val functional_compilation : string -> mode -> compilation_funs -> typ -> term
  val force_modes_and_functions : string -> (mode * (string * bool)) list -> theory -> theory
  val force_modes_and_compilations : string ->
    (mode * ((compilation_funs -> typ -> term) * bool)) list -> theory -> theory
  val preprocess_intro : theory -> thm -> thm
  val print_stored_rules : Proof.context -> unit
  val print_all_modes : compilation -> Proof.context -> unit
  val mk_casesrule : Proof.context -> term -> thm list -> term

  val put_pred_result : (unit -> term Predicate.pred) -> Proof.context -> Proof.context
  val put_pred_random_result : (unit -> int * int -> term Predicate.pred * (int * int)) ->
    Proof.context -> Proof.context
  val put_dseq_result : (unit -> term DSequence.dseq) -> Proof.context -> Proof.context
  val put_dseq_random_result : (unit -> int -> int -> int * int -> term DSequence.dseq * (int * int)) ->
    Proof.context -> Proof.context
  val put_lseq_random_result :
    (unit -> int -> int -> int * int -> int -> term Lazy_Sequence.lazy_sequence) ->
    Proof.context -> Proof.context
  val put_lseq_random_stats_result :
    (unit -> int -> int -> int * int -> int -> (term * int) Lazy_Sequence.lazy_sequence) ->
    Proof.context -> Proof.context

  val code_pred_intro_attrib : attribute
  (* used by Quickcheck_Generator *) 
  (* temporary for testing of the compilation *)
  val add_equations : options -> string list -> theory -> theory
  val add_depth_limited_random_equations : options -> string list -> theory -> theory
  val add_random_dseq_equations : options -> string list -> theory -> theory
  val add_new_random_dseq_equations : options -> string list -> theory -> theory
  val mk_tracing : string -> term -> term
  val prepare_intrs : options -> Proof.context -> string list -> thm list ->
    ((string * typ) list * string list * string list * (string * mode list) list *
      (string *  (Term.term list * Predicate_Compile_Aux.indprem list) list) list)
  type mode_analysis_options =
   {use_generators : bool,
    reorder_premises : bool,
    infer_pos_and_neg_modes : bool}  
  datatype mode_derivation = Mode_App of mode_derivation * mode_derivation | Context of mode
    | Mode_Pair of mode_derivation * mode_derivation | Term of mode
  val head_mode_of : mode_derivation -> mode
  type moded_clause = term list * (Predicate_Compile_Aux.indprem * mode_derivation) list
  type 'a pred_mode_table = (string * ((bool * mode) * 'a) list) list

  val infer_modes : 
    mode_analysis_options -> options ->
     (string -> Predicate_Compile_Aux.mode list) * (string -> Predicate_Compile_Aux.mode list)
       * (string -> Predicate_Compile_Aux.mode -> bool) -> Proof.context -> (string * typ) list ->
      (string * mode list) list ->
      string list -> (string * (Term.term list * Predicate_Compile_Aux.indprem list) list) list ->
      ((moded_clause list pred_mode_table * (string * mode list) list) * string list)
end;

structure Predicate_Compile_Core : PREDICATE_COMPILE_CORE =
struct

open Predicate_Compile_Aux;

(** auxiliary **)

(* debug stuff *)

fun print_tac options s = 
  if show_proof_trace options then Tactical.print_tac s else Seq.single;

fun assert b = if not b then raise Fail "Assertion failed" else warning "Assertion holds"

datatype assertion = Max_number_of_subgoals of int
fun assert_tac (Max_number_of_subgoals i) st =
  if (nprems_of st <= i) then Seq.single st
  else raise Fail ("assert_tac: Numbers of subgoals mismatch at goal state :"
    ^ "\n" ^ Pretty.string_of (Pretty.chunks
      (Goal_Display.pretty_goals_without_context st)));

(** fundamentals **)

(* syntactic operations *)

fun mk_eq (x, xs) =
  let fun mk_eqs _ [] = []
        | mk_eqs a (b::cs) =
            HOLogic.mk_eq (Free (a, fastype_of b), b) :: mk_eqs a cs
  in mk_eqs x xs end;

fun mk_scomp (t, u) =
  let
    val T = fastype_of t
    val U = fastype_of u
    val [A] = binder_types T
    val D = body_type U                   
  in 
    Const (@{const_name "scomp"}, T --> U --> A --> D) $ t $ u
  end;

fun dest_funT (Type ("fun",[S, T])) = (S, T)
  | dest_funT T = raise TYPE ("dest_funT", [T], [])
 
fun mk_fun_comp (t, u) =
  let
    val (_, B) = dest_funT (fastype_of t)
    val (C, A) = dest_funT (fastype_of u)
  in
    Const(@{const_name "Fun.comp"}, (A --> B) --> (C --> A) --> C --> B) $ t $ u
  end;

fun dest_randomT (Type ("fun", [@{typ Random.seed},
  Type (@{type_name Product_Type.prod}, [Type (@{type_name Product_Type.prod}, [T, @{typ "unit => Code_Evaluation.term"}]) ,@{typ Random.seed}])])) = T
  | dest_randomT T = raise TYPE ("dest_randomT", [T], [])

fun mk_tracing s t =
  Const(@{const_name Code_Evaluation.tracing},
    @{typ String.literal} --> (fastype_of t) --> (fastype_of t)) $ (HOLogic.mk_literal s) $ t

val strip_intro_concl = (strip_comb o HOLogic.dest_Trueprop o Logic.strip_imp_concl o prop_of)

(* derivation trees for modes of premises *)

datatype mode_derivation = Mode_App of mode_derivation * mode_derivation | Context of mode
  | Mode_Pair of mode_derivation * mode_derivation | Term of mode

fun string_of_derivation (Mode_App (m1, m2)) =
  "App (" ^ string_of_derivation m1 ^ ", " ^ string_of_derivation m2 ^ ")"
  | string_of_derivation (Mode_Pair (m1, m2)) =
  "Pair (" ^ string_of_derivation m1 ^ ", " ^ string_of_derivation m2 ^ ")"
  | string_of_derivation (Term m) = "Term (" ^ string_of_mode m ^ ")"
  | string_of_derivation (Context m) = "Context (" ^ string_of_mode m ^ ")"

fun strip_mode_derivation deriv =
  let
    fun strip (Mode_App (deriv1, deriv2)) ds = strip deriv1 (deriv2 :: ds)
      | strip deriv ds = (deriv, ds)
  in
    strip deriv []
  end

fun mode_of (Context m) = m
  | mode_of (Term m) = m
  | mode_of (Mode_App (d1, d2)) =
    (case mode_of d1 of Fun (m, m') =>
        (if eq_mode (m, mode_of d2) then m' else raise Fail "mode_of: derivation has mismatching modes")
      | _ => raise Fail "mode_of: derivation has a non-functional mode")
  | mode_of (Mode_Pair (d1, d2)) =
    Pair (mode_of d1, mode_of d2)

fun head_mode_of deriv = mode_of (fst (strip_mode_derivation deriv))

fun param_derivations_of deriv =
  let
    val (_, argument_derivs) = strip_mode_derivation deriv
    fun param_derivation (Mode_Pair (m1, m2)) =
        param_derivation m1 @ param_derivation m2
      | param_derivation (Term _) = []
      | param_derivation m = [m]
  in
    maps param_derivation argument_derivs
  end

fun collect_context_modes (Mode_App (m1, m2)) =
      collect_context_modes m1 @ collect_context_modes m2
  | collect_context_modes (Mode_Pair (m1, m2)) =
      collect_context_modes m1 @ collect_context_modes m2
  | collect_context_modes (Context m) = [m]
  | collect_context_modes (Term _) = []

(* representation of inferred clauses with modes *)

type moded_clause = term list * (indprem * mode_derivation) list

type 'a pred_mode_table = (string * ((bool * mode) * 'a) list) list

(* book-keeping *)

datatype predfun_data = PredfunData of {
  definition : thm,
  intro : thm,
  elim : thm,
  neg_intro : thm option
};

fun rep_predfun_data (PredfunData data) = data;

fun mk_predfun_data (definition, ((intro, elim), neg_intro)) =
  PredfunData {definition = definition, intro = intro, elim = elim, neg_intro = neg_intro}

datatype pred_data = PredData of {
  intros : (string option * thm) list,
  elim : thm option,
  preprocessed : bool,
  function_names : (compilation * (mode * string) list) list,
  predfun_data : (mode * predfun_data) list,
  needs_random : mode list
};

fun rep_pred_data (PredData data) = data;

fun mk_pred_data (((intros, elim), preprocessed), (function_names, (predfun_data, needs_random))) =
  PredData {intros = intros, elim = elim, preprocessed = preprocessed,
    function_names = function_names, predfun_data = predfun_data, needs_random = needs_random}

fun map_pred_data f (PredData {intros, elim, preprocessed, function_names, predfun_data, needs_random}) =
  mk_pred_data (f (((intros, elim), preprocessed), (function_names, (predfun_data, needs_random))))

fun eq_option eq (NONE, NONE) = true
  | eq_option eq (SOME x, SOME y) = eq (x, y)
  | eq_option eq _ = false

fun eq_pred_data (PredData d1, PredData d2) = 
  eq_list (eq_pair (op =) Thm.eq_thm) (#intros d1, #intros d2) andalso
  eq_option Thm.eq_thm (#elim d1, #elim d2)

structure PredData = Theory_Data
(
  type T = pred_data Graph.T;
  val empty = Graph.empty;
  val extend = I;
  val merge = Graph.merge eq_pred_data;
);

(* queries *)

fun lookup_pred_data ctxt name =
  Option.map rep_pred_data (try (Graph.get_node (PredData.get (ProofContext.theory_of ctxt))) name)

fun the_pred_data ctxt name = case lookup_pred_data ctxt name
 of NONE => error ("No such predicate " ^ quote name)  
  | SOME data => data;

val is_registered = is_some oo lookup_pred_data

val all_preds_of = Graph.keys o PredData.get o ProofContext.theory_of

val intros_of = map snd o #intros oo the_pred_data

val names_of = map fst o #intros oo the_pred_data

fun the_elim_of ctxt name = case #elim (the_pred_data ctxt name)
 of NONE => error ("No elimination rule for predicate " ^ quote name)
  | SOME thm => thm
  
val has_elim = is_some o #elim oo the_pred_data

fun function_names_of compilation ctxt name =
  case AList.lookup (op =) (#function_names (the_pred_data ctxt name)) compilation of
    NONE => error ("No " ^ string_of_compilation compilation
      ^ "functions defined for predicate " ^ quote name)
  | SOME fun_names => fun_names

fun function_name_of compilation ctxt name mode =
  case AList.lookup eq_mode
    (function_names_of compilation ctxt name) mode of
    NONE => error ("No " ^ string_of_compilation compilation
      ^ " function defined for mode " ^ string_of_mode mode ^ " of predicate " ^ quote name)
  | SOME function_name => function_name

fun modes_of compilation ctxt name = map fst (function_names_of compilation ctxt name)

fun all_modes_of compilation ctxt =
  map_filter (fn name => Option.map (pair name) (try (modes_of compilation ctxt) name))
    (all_preds_of ctxt)

val all_random_modes_of = all_modes_of Random

fun defined_functions compilation ctxt name = case lookup_pred_data ctxt name of
    NONE => false
  | SOME data => AList.defined (op =) (#function_names data) compilation

fun needs_random ctxt s m =
  member (op =) (#needs_random (the_pred_data ctxt s)) m

fun lookup_predfun_data ctxt name mode =
  Option.map rep_predfun_data
    (AList.lookup (op =) (#predfun_data (the_pred_data ctxt name)) mode)

fun the_predfun_data ctxt name mode =
  case lookup_predfun_data ctxt name mode of
    NONE => error ("No function defined for mode " ^ string_of_mode mode ^
      " of predicate " ^ name)
  | SOME data => data;

val predfun_definition_of = #definition ooo the_predfun_data

val predfun_intro_of = #intro ooo the_predfun_data

val predfun_elim_of = #elim ooo the_predfun_data

val predfun_neg_intro_of = #neg_intro ooo the_predfun_data

val intros_graph_of =
  Graph.map (K (map snd o #intros o rep_pred_data)) o PredData.get o ProofContext.theory_of

(* diagnostic display functions *)

fun print_modes options modes =
  if show_modes options then
    tracing ("Inferred modes:\n" ^
      cat_lines (map (fn (s, ms) => s ^ ": " ^ commas (map
        (fn (p, m) => string_of_mode m ^ (if p then "pos" else "neg")) ms)) modes))
  else ()

fun print_pred_mode_table string_of_entry pred_mode_table =
  let
    fun print_mode pred ((pol, mode), entry) =  "mode : " ^ string_of_mode mode
      ^ string_of_entry pred mode entry
    fun print_pred (pred, modes) =
      "predicate " ^ pred ^ ": " ^ cat_lines (map (print_mode pred) modes)
    val _ = tracing (cat_lines (map print_pred pred_mode_table))
  in () end;

fun string_of_prem ctxt (Prem t) =
    (Syntax.string_of_term ctxt t) ^ "(premise)"
  | string_of_prem ctxt (Negprem t) =
    (Syntax.string_of_term ctxt (HOLogic.mk_not t)) ^ "(negative premise)"
  | string_of_prem ctxt (Sidecond t) =
    (Syntax.string_of_term ctxt t) ^ "(sidecondition)"
  | string_of_prem ctxt _ = raise Fail "string_of_prem: unexpected input"

fun string_of_clause ctxt pred (ts, prems) =
  (space_implode " --> "
  (map (string_of_prem ctxt) prems)) ^ " --> " ^ pred ^ " "
   ^ (space_implode " " (map (Syntax.string_of_term ctxt) ts))

fun print_compiled_terms options ctxt =
  if show_compilation options then
    print_pred_mode_table (fn _ => fn _ => Syntax.string_of_term ctxt)
  else K ()

fun print_stored_rules ctxt =
  let
    val preds = Graph.keys (PredData.get (ProofContext.theory_of ctxt))
    fun print pred () = let
      val _ = writeln ("predicate: " ^ pred)
      val _ = writeln ("introrules: ")
      val _ = fold (fn thm => fn u => writeln (Display.string_of_thm ctxt thm))
        (rev (intros_of ctxt pred)) ()
    in
      if (has_elim ctxt pred) then
        writeln ("elimrule: " ^ Display.string_of_thm ctxt (the_elim_of ctxt pred))
      else
        writeln ("no elimrule defined")
    end
  in
    fold print preds ()
  end;

fun print_all_modes compilation ctxt =
  let
    val _ = writeln ("Inferred modes:")
    fun print (pred, modes) u =
      let
        val _ = writeln ("predicate: " ^ pred)
        val _ = writeln ("modes: " ^ (commas (map string_of_mode modes)))
      in u end
  in
    fold print (all_modes_of compilation ctxt) ()
  end

(* validity checks *)

fun check_expected_modes preds options modes =
  case expected_modes options of
    SOME (s, ms) => (case AList.lookup (op =) modes s of
      SOME modes =>
        let
          val modes' = map snd modes
        in
          if not (eq_set eq_mode (ms, modes')) then
            error ("expected modes were not inferred:\n"
            ^ "  inferred modes for " ^ s ^ ": " ^ commas (map string_of_mode modes')  ^ "\n"
            ^ "  expected modes for " ^ s ^ ": " ^ commas (map string_of_mode ms))
          else ()
        end
      | NONE => ())
  | NONE => ()

fun check_proposed_modes preds options modes errors =
  map (fn (s, _) => case proposed_modes options s of
    SOME ms => (case AList.lookup (op =) modes s of
      SOME inferred_ms =>
        let
          val preds_without_modes = map fst (filter (null o snd) modes)
          val modes' = map snd inferred_ms
        in
          if not (eq_set eq_mode (ms, modes')) then
            error ("expected modes were not inferred:\n"
            ^ "  inferred modes for " ^ s ^ ": " ^ commas (map string_of_mode modes')  ^ "\n"
            ^ "  expected modes for " ^ s ^ ": " ^ commas (map string_of_mode ms) ^ "\n"
            ^ (if show_invalid_clauses options then
            ("For the following clauses, the following modes could not be inferred: " ^ "\n"
            ^ cat_lines errors) else "") ^
            (if not (null preds_without_modes) then
              "\n" ^ "No mode inferred for the predicates " ^ commas preds_without_modes
            else ""))
          else ()
        end
      | NONE => ())
  | NONE => ()) preds

fun check_matches_type ctxt predname T ms =
  let
    fun check (m as Fun (m1, m2)) (Type("fun", [T1,T2])) = check m1 T1 andalso check m2 T2
      | check m (T as Type("fun", _)) =
        if body_type T = @{typ bool} then false else (m = Input orelse m = Output)
      | check (Pair (m1, m2)) (Type (@{type_name Product_Type.prod}, [T1, T2])) =
          check m1 T1 andalso check m2 T2 
      | check Input T = true
      | check Output T = true
      | check Bool @{typ bool} = true
      | check _ _ = false
    val _ = map
      (fn mode =>
        if (forall (uncurry check) (strip_fun_mode mode ~~ binder_types T)) then ()
        else error (string_of_mode mode ^ " is not a valid mode for " ^ Syntax.string_of_typ ctxt T
        ^ " at predicate " ^ predname)) ms
  in
    ms
  end


(* importing introduction rules *)

fun unify_consts thy cs intr_ts =
  (let
     val add_term_consts_2 = fold_aterms (fn Const c => insert (op =) c | _ => I);
     fun varify (t, (i, ts)) =
       let val t' = map_types (Logic.incr_tvar (i + 1)) (#2 (Type.varify_global [] t))
       in (maxidx_of_term t', t'::ts) end;
     val (i, cs') = List.foldr varify (~1, []) cs;
     val (i', intr_ts') = List.foldr varify (i, []) intr_ts;
     val rec_consts = fold add_term_consts_2 cs' [];
     val intr_consts = fold add_term_consts_2 intr_ts' [];
     fun unify (cname, cT) =
       let val consts = map snd (filter (fn c => fst c = cname) intr_consts)
       in fold (Sign.typ_unify thy) ((replicate (length consts) cT) ~~ consts) end;
     val (env, _) = fold unify rec_consts (Vartab.empty, i');
     val subst = map_types (Envir.norm_type env)
   in (map subst cs', map subst intr_ts')
   end) handle Type.TUNIFY =>
     (warning "Occurrences of recursive constant have non-unifiable types"; (cs, intr_ts));

fun import_intros inp_pred [] ctxt =
  let
    val ([outp_pred], ctxt') = Variable.import_terms true [inp_pred] ctxt
    val T = fastype_of outp_pred
    val paramTs = ho_argsT_of_typ (binder_types T)
    val (param_names, ctxt'') = Variable.variant_fixes
      (map (fn i => "p" ^ (string_of_int i)) (1 upto (length paramTs))) ctxt'
    val params = map2 (curry Free) param_names paramTs
  in
    (((outp_pred, params), []), ctxt')
  end
  | import_intros inp_pred (th :: ths) ctxt =
    let
      val ((_, [th']), ctxt') = Variable.import true [th] ctxt
      val thy = ProofContext.theory_of ctxt'
      val (pred, args) = strip_intro_concl th'
      val T = fastype_of pred
      val ho_args = ho_args_of_typ T args
      fun subst_of (pred', pred) =
        let
          val subst = Sign.typ_match thy (fastype_of pred', fastype_of pred) Vartab.empty
            handle Type.TYPE_MATCH => error ("Type mismatch of predicate " ^ fst (dest_Const pred)
            ^ " (trying to match " ^ Syntax.string_of_typ ctxt (fastype_of pred')
            ^ " and " ^ Syntax.string_of_typ ctxt (fastype_of pred) ^ ")"
            ^ " in " ^ Display.string_of_thm ctxt th)
        in map (fn (indexname, (s, T)) => ((indexname, s), T)) (Vartab.dest subst) end
      fun instantiate_typ th =
        let
          val (pred', _) = strip_intro_concl th
          val _ = if not (fst (dest_Const pred) = fst (dest_Const pred')) then
            raise Fail "Trying to instantiate another predicate" else ()
        in Thm.certify_instantiate (subst_of (pred', pred), []) th end;
      fun instantiate_ho_args th =
        let
          val (_, args') = (strip_comb o HOLogic.dest_Trueprop o Logic.strip_imp_concl o prop_of) th
          val ho_args' = map dest_Var (ho_args_of_typ T args')
        in Thm.certify_instantiate ([], ho_args' ~~ ho_args) th end
      val outp_pred =
        Term_Subst.instantiate (subst_of (inp_pred, pred), []) inp_pred
      val ((_, ths'), ctxt1) =
        Variable.import false (map (instantiate_typ #> instantiate_ho_args) ths) ctxt'
    in
      (((outp_pred, ho_args), th' :: ths'), ctxt1)
    end

(* generation of case rules from user-given introduction rules *)

fun mk_args2 (Type (@{type_name Product_Type.prod}, [T1, T2])) st =
    let
      val (t1, st') = mk_args2 T1 st
      val (t2, st'') = mk_args2 T2 st'
    in
      (HOLogic.mk_prod (t1, t2), st'')
    end
  (*| mk_args2 (T as Type ("fun", _)) (params, ctxt) = 
    let
      val (S, U) = strip_type T
    in
      if U = HOLogic.boolT then
        (hd params, (tl params, ctxt))
      else
        let
          val ([x], ctxt') = Variable.variant_fixes ["x"] ctxt
        in
          (Free (x, T), (params, ctxt'))
        end
    end*)
  | mk_args2 T (params, ctxt) =
    let
      val ([x], ctxt') = Variable.variant_fixes ["x"] ctxt
    in
      (Free (x, T), (params, ctxt'))
    end

fun mk_casesrule ctxt pred introrules =
  let
    (* TODO: can be simplified if parameters are not treated specially ? *)
    val (((pred, params), intros_th), ctxt1) = import_intros pred introrules ctxt
    (* TODO: distinct required ? -- test case with more than one parameter! *)
    val params = distinct (op aconv) params
    val intros = map prop_of intros_th
    val ([propname], ctxt2) = Variable.variant_fixes ["thesis"] ctxt1
    val prop = HOLogic.mk_Trueprop (Free (propname, HOLogic.boolT))
    val argsT = binder_types (fastype_of pred)
    (* TODO: can be simplified if parameters are not treated specially ? <-- see uncommented code! *)
    val (argvs, _) = fold_map mk_args2 argsT (params, ctxt2)
    fun mk_case intro =
      let
        val (_, args) = (strip_comb o HOLogic.dest_Trueprop o Logic.strip_imp_concl) intro
        val prems = Logic.strip_imp_prems intro
        val eqprems =
          map2 (HOLogic.mk_Trueprop oo (curry HOLogic.mk_eq)) argvs args
        val frees = map Free (fold Term.add_frees (args @ prems) [])
      in fold Logic.all frees (Logic.list_implies (eqprems @ prems, prop)) end
    val assm = HOLogic.mk_Trueprop (list_comb (pred, argvs))
    val cases = map mk_case intros
  in Logic.list_implies (assm :: cases, prop) end;

fun dest_conjunct_prem th =
  case HOLogic.dest_Trueprop (prop_of th) of
    (Const (@{const_name HOL.conj}, _) $ t $ t') =>
      dest_conjunct_prem (th RS @{thm conjunct1})
        @ dest_conjunct_prem (th RS @{thm conjunct2})
    | _ => [th]

fun prove_casesrule ctxt (pred, (pre_cases_rule, nparams)) cases_rule =
  let
    val thy = ProofContext.theory_of ctxt
    val nargs = length (binder_types (fastype_of pred))
    fun PEEK f dependent_tactic st = dependent_tactic (f st) st
    fun meta_eq_of th = th RS @{thm eq_reflection}
    val tuple_rew_rules = map meta_eq_of [@{thm fst_conv}, @{thm snd_conv}, @{thm Pair_eq}]
    fun instantiate i n {context = ctxt, params = p, prems = prems,
      asms = a, concl = cl, schematics = s}  =
      let
        fun term_pair_of (ix, (ty,t)) = (Var (ix,ty), t)
        fun inst_of_matches tts = fold (Pattern.match thy) tts (Vartab.empty, Vartab.empty)
          |> snd |> Vartab.dest |> map (pairself (cterm_of thy) o term_pair_of)
        val (cases, (eqs, prems)) = apsnd (chop (nargs - nparams)) (chop n prems)
        val case_th = MetaSimplifier.simplify true
          (@{thm Predicate.eq_is_eq} :: map meta_eq_of eqs) (nth cases (i - 1))
        val prems' = maps (dest_conjunct_prem o MetaSimplifier.simplify true tuple_rew_rules) prems
        val pats = map (swap o HOLogic.dest_eq o HOLogic.dest_Trueprop) (take nargs (prems_of case_th))
        val case_th' = Thm.instantiate ([], inst_of_matches pats) case_th
          OF (replicate nargs @{thm refl})
        val thesis =
          Thm.instantiate ([], inst_of_matches (prems_of case_th' ~~ map prop_of prems')) case_th'
            OF prems'
      in
        (rtac thesis 1)
      end
    val tac =
      etac pre_cases_rule 1
      THEN
      (PEEK nprems_of
        (fn n =>
          ALLGOALS (fn i =>
            MetaSimplifier.rewrite_goal_tac [@{thm split_paired_all}] i
            THEN (SUBPROOF (instantiate i n) ctxt i))))
  in
    Goal.prove ctxt (Term.add_free_names cases_rule []) [] cases_rule (fn _ => tac)
  end

(** preprocessing rules **)

fun Trueprop_conv cv ct =
  case Thm.term_of ct of
    Const (@{const_name Trueprop}, _) $ _ => Conv.arg_conv cv ct  
  | _ => raise Fail "Trueprop_conv"

fun preprocess_equality thy rule =
  Conv.fconv_rule
    (imp_prems_conv
      (Trueprop_conv (Conv.try_conv (Conv.rewr_conv (Thm.symmetric @{thm Predicate.eq_is_eq})))))
    (Thm.transfer thy rule)

fun preprocess_intro thy = expand_tuples thy #> preprocess_equality thy

(* fetching introduction rules or registering introduction rules *)

val no_compilation = ([], ([], []))

fun fetch_pred_data ctxt name =
  case try (Inductive.the_inductive ctxt) name of
    SOME (info as (_, result)) => 
      let
        fun is_intro_of intro =
          let
            val (const, _) = strip_comb (HOLogic.dest_Trueprop (concl_of intro))
          in (fst (dest_Const const) = name) end;
        val thy = ProofContext.theory_of ctxt
        val intros = map (preprocess_intro thy) (filter is_intro_of (#intrs result))
        val index = find_index (fn s => s = name) (#names (fst info))
        val pre_elim = nth (#elims result) index
        val pred = nth (#preds result) index
        val elim_t = mk_casesrule ctxt pred intros
        val nparams = length (Inductive.params_of (#raw_induct result))
        val elim = prove_casesrule ctxt (pred, (pre_elim, nparams)) elim_t
      in
        mk_pred_data (((map (pair NONE) intros, SOME elim), true), no_compilation)
      end
  | NONE => error ("No such predicate: " ^ quote name)

fun add_predfun_data name mode data =
  let
    val add = (apsnd o apsnd o apfst) (cons (mode, mk_predfun_data data))
  in PredData.map (Graph.map_node name (map_pred_data add)) end

fun is_inductive_predicate ctxt name =
  is_some (try (Inductive.the_inductive ctxt) name)

fun depending_preds_of ctxt (key, value) =
  let
    val intros = map (Thm.prop_of o snd) ((#intros o rep_pred_data) value)
  in
    fold Term.add_const_names intros []
      |> (fn cs =>
        if member (op =) cs @{const_name "HOL.eq"} then
          insert (op =) @{const_name Predicate.eq} cs
        else cs)
      |> filter (fn c => (not (c = key)) andalso
        (is_inductive_predicate ctxt c orelse is_registered ctxt c))
  end;

fun add_intro (opt_case_name, thm) thy =
  let
    val (name, T) = dest_Const (fst (strip_intro_concl thm))
    fun cons_intro gr =
     case try (Graph.get_node gr) name of
       SOME pred_data => Graph.map_node name (map_pred_data
         (apfst (apfst (apfst (fn intros => intros @ [(opt_case_name, thm)]))))) gr
     | NONE => Graph.new_node (name, mk_pred_data ((([(opt_case_name, thm)], NONE), false), no_compilation)) gr
  in PredData.map cons_intro thy end

fun set_elim thm =
  let
    val (name, _) = dest_Const (fst 
      (strip_comb (HOLogic.dest_Trueprop (hd (prems_of thm)))))
  in PredData.map (Graph.map_node name (map_pred_data (apfst (apfst (apsnd (K (SOME thm))))))) end

fun register_predicate (constname, intros, elim) thy =
  let
    val named_intros = map (pair NONE) intros
  in
    if not (member (op =) (Graph.keys (PredData.get thy)) constname) then
      PredData.map
        (Graph.new_node (constname,
          mk_pred_data (((named_intros, SOME elim), false), no_compilation))) thy
    else thy
  end

fun register_intros (constname, pre_intros) thy =
  let
    val T = Sign.the_const_type thy constname
    fun constname_of_intro intr = fst (dest_Const (fst (strip_intro_concl intr)))
    val _ = if not (forall (fn intr => constname_of_intro intr = constname) pre_intros) then
      error ("register_intros: Introduction rules of different constants are used\n" ^
        "expected rules for " ^ constname ^ ", but received rules for " ^
          commas (map constname_of_intro pre_intros))
      else ()
    val pred = Const (constname, T)
    val pre_elim = 
      (Drule.export_without_context o Skip_Proof.make_thm thy)
      (mk_casesrule (ProofContext.init_global thy) pred pre_intros)
  in register_predicate (constname, pre_intros, pre_elim) thy end

fun defined_function_of compilation pred =
  let
    val set = (apsnd o apfst) (cons (compilation, []))
  in
    PredData.map (Graph.map_node pred (map_pred_data set))
  end

fun set_function_name compilation pred mode name =
  let
    val set = (apsnd o apfst)
      (AList.map_default (op =) (compilation, [(mode, name)]) (cons (mode, name)))
  in
    PredData.map (Graph.map_node pred (map_pred_data set))
  end

fun set_needs_random name modes =
  let
    val set = (apsnd o apsnd o apsnd) (K modes)
  in
    PredData.map (Graph.map_node name (map_pred_data set))
  end

(* registration of alternative function names *)

structure Alt_Compilations_Data = Theory_Data
(
  type T = (mode * (compilation_funs -> typ -> term)) list Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data : T = Symtab.merge (K true) data;
);

fun alternative_compilation_of_global thy pred_name mode =
  AList.lookup eq_mode (Symtab.lookup_list (Alt_Compilations_Data.get thy) pred_name) mode

fun alternative_compilation_of ctxt pred_name mode =
  AList.lookup eq_mode
    (Symtab.lookup_list (Alt_Compilations_Data.get (ProofContext.theory_of ctxt)) pred_name) mode

fun force_modes_and_compilations pred_name compilations =
  let
    (* thm refl is a dummy thm *)
    val modes = map fst compilations
    val (needs_random, non_random_modes) = pairself (map fst)
      (List.partition (fn (m, (fun_name, random)) => random) compilations)
    val non_random_dummys = map (rpair "dummy") non_random_modes
    val all_dummys = map (rpair "dummy") modes
    val dummy_function_names = map (rpair all_dummys) Predicate_Compile_Aux.random_compilations
      @ map (rpair non_random_dummys) Predicate_Compile_Aux.non_random_compilations
    val alt_compilations = map (apsnd fst) compilations
  in
    PredData.map (Graph.new_node
      (pred_name, mk_pred_data ((([], SOME @{thm refl}), true), (dummy_function_names, ([], needs_random)))))
    #> Alt_Compilations_Data.map (Symtab.insert (K false) (pred_name, alt_compilations))
  end

fun functional_compilation fun_name mode compfuns T =
  let
    val (inpTs, outpTs) = split_map_modeT (fn _ => fn T => (SOME T, NONE))
      mode (binder_types T)
    val bs = map (pair "x") inpTs
    val bounds = map Bound (rev (0 upto (length bs) - 1))
    val f = Const (fun_name, inpTs ---> HOLogic.mk_tupleT outpTs)
  in list_abs (bs, mk_single compfuns (list_comb (f, bounds))) end

fun register_alternative_function pred_name mode fun_name =
  Alt_Compilations_Data.map (Symtab.insert_list (eq_pair eq_mode (K false))
    (pred_name, (mode, functional_compilation fun_name mode)))

fun force_modes_and_functions pred_name fun_names =
  force_modes_and_compilations pred_name
    (map (fn (mode, (fun_name, random)) => (mode, (functional_compilation fun_name mode, random)))
    fun_names)

(* compilation modifiers *)

structure Comp_Mod =
struct

datatype comp_modifiers = Comp_Modifiers of
{
  compilation : compilation,
  function_name_prefix : string,
  compfuns : compilation_funs,
  mk_random : typ -> term list -> term,
  modify_funT : typ -> typ,
  additional_arguments : string list -> term list,
  wrap_compilation : compilation_funs -> string -> typ -> mode -> term list -> term -> term,
  transform_additional_arguments : indprem -> term list -> term list
}

fun dest_comp_modifiers (Comp_Modifiers c) = c

val compilation = #compilation o dest_comp_modifiers
val function_name_prefix = #function_name_prefix o dest_comp_modifiers
val compfuns = #compfuns o dest_comp_modifiers

val mk_random = #mk_random o dest_comp_modifiers
val funT_of' = funT_of o compfuns
val modify_funT = #modify_funT o dest_comp_modifiers
fun funT_of comp mode = modify_funT comp o funT_of' comp mode

val additional_arguments = #additional_arguments o dest_comp_modifiers
val wrap_compilation = #wrap_compilation o dest_comp_modifiers
val transform_additional_arguments = #transform_additional_arguments o dest_comp_modifiers

end;

val depth_limited_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = Depth_Limited,
  function_name_prefix = "depth_limited_",
  compfuns = PredicateCompFuns.compfuns,
  mk_random = (fn _ => error "no random generation"),
  additional_arguments = fn names =>
    let
      val depth_name = Name.variant names "depth"
    in [Free (depth_name, @{typ code_numeral})] end,
  modify_funT = (fn T => let val (Ts, U) = strip_type T
  val Ts' = [@{typ code_numeral}] in (Ts @ Ts') ---> U end),
  wrap_compilation =
    fn compfuns => fn s => fn T => fn mode => fn additional_arguments => fn compilation =>
    let
      val [depth] = additional_arguments
      val (_, Ts) = split_modeT' mode (binder_types T)
      val T' = mk_predT compfuns (HOLogic.mk_tupleT Ts)
      val if_const = Const (@{const_name "If"}, @{typ bool} --> T' --> T' --> T')
    in
      if_const $ HOLogic.mk_eq (depth, @{term "0 :: code_numeral"})
        $ mk_bot compfuns (dest_predT compfuns T')
        $ compilation
    end,
  transform_additional_arguments =
    fn prem => fn additional_arguments =>
    let
      val [depth] = additional_arguments
      val depth' =
        Const (@{const_name Groups.minus}, @{typ "code_numeral => code_numeral => code_numeral"})
          $ depth $ Const (@{const_name Groups.one}, @{typ "Code_Numeral.code_numeral"})
    in [depth'] end
  }

val random_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = Random,
  function_name_prefix = "random_",
  compfuns = PredicateCompFuns.compfuns,
  mk_random = (fn T => fn additional_arguments =>
  list_comb (Const(@{const_name Quickcheck.iter},
  [@{typ code_numeral}, @{typ code_numeral}, @{typ Random.seed}] ---> 
    PredicateCompFuns.mk_predT T), additional_arguments)),
  modify_funT = (fn T =>
    let
      val (Ts, U) = strip_type T
      val Ts' = [@{typ code_numeral}, @{typ code_numeral}, @{typ "code_numeral * code_numeral"}]
    in (Ts @ Ts') ---> U end),
  additional_arguments = (fn names =>
    let
      val [nrandom, size, seed] = Name.variant_list names ["nrandom", "size", "seed"]
    in
      [Free (nrandom, @{typ code_numeral}), Free (size, @{typ code_numeral}),
        Free (seed, @{typ "code_numeral * code_numeral"})]
    end),
  wrap_compilation = K (K (K (K (K I))))
    : (compilation_funs -> string -> typ -> mode -> term list -> term -> term),
  transform_additional_arguments = K I : (indprem -> term list -> term list)
  }

val depth_limited_random_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = Depth_Limited_Random,
  function_name_prefix = "depth_limited_random_",
  compfuns = PredicateCompFuns.compfuns,
  mk_random = (fn T => fn additional_arguments =>
  list_comb (Const(@{const_name Quickcheck.iter},
  [@{typ code_numeral}, @{typ code_numeral}, @{typ Random.seed}] ---> 
    PredicateCompFuns.mk_predT T), tl additional_arguments)),
  modify_funT = (fn T =>
    let
      val (Ts, U) = strip_type T
      val Ts' = [@{typ code_numeral}, @{typ code_numeral}, @{typ code_numeral},
        @{typ "code_numeral * code_numeral"}]
    in (Ts @ Ts') ---> U end),
  additional_arguments = (fn names =>
    let
      val [depth, nrandom, size, seed] = Name.variant_list names ["depth", "nrandom", "size", "seed"]
    in
      [Free (depth, @{typ code_numeral}), Free (nrandom, @{typ code_numeral}),
        Free (size, @{typ code_numeral}), Free (seed, @{typ "code_numeral * code_numeral"})]
    end),
  wrap_compilation =
  fn compfuns => fn s => fn T => fn mode => fn additional_arguments => fn compilation =>
    let
      val depth = hd (additional_arguments)
      val (_, Ts) = split_map_modeT (fn m => fn T => (SOME (funT_of compfuns m T), NONE))
        mode (binder_types T)
      val T' = mk_predT compfuns (HOLogic.mk_tupleT Ts)
      val if_const = Const (@{const_name "If"}, @{typ bool} --> T' --> T' --> T')
    in
      if_const $ HOLogic.mk_eq (depth, @{term "0 :: code_numeral"})
        $ mk_bot compfuns (dest_predT compfuns T')
        $ compilation
    end,
  transform_additional_arguments =
    fn prem => fn additional_arguments =>
    let
      val [depth, nrandom, size, seed] = additional_arguments
      val depth' =
        Const (@{const_name Groups.minus}, @{typ "code_numeral => code_numeral => code_numeral"})
          $ depth $ Const (@{const_name Groups.one}, @{typ "Code_Numeral.code_numeral"})
    in [depth', nrandom, size, seed] end
}

val predicate_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = Pred,
  function_name_prefix = "",
  compfuns = PredicateCompFuns.compfuns,
  mk_random = (fn _ => error "no random generation"),
  modify_funT = I,
  additional_arguments = K [],
  wrap_compilation = K (K (K (K (K I))))
   : (compilation_funs -> string -> typ -> mode -> term list -> term -> term),
  transform_additional_arguments = K I : (indprem -> term list -> term list)
  }

val annotated_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = Annotated,
  function_name_prefix = "annotated_",
  compfuns = PredicateCompFuns.compfuns,
  mk_random = (fn _ => error "no random generation"),
  modify_funT = I,
  additional_arguments = K [],
  wrap_compilation =
    fn compfuns => fn s => fn T => fn mode => fn additional_arguments => fn compilation =>
      mk_tracing ("calling predicate " ^ s ^
        " with mode " ^ string_of_mode mode) compilation,
  transform_additional_arguments = K I : (indprem -> term list -> term list)
  }

val dseq_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = DSeq,
  function_name_prefix = "dseq_",
  compfuns = DSequence_CompFuns.compfuns,
  mk_random = (fn _ => error "no random generation"),
  modify_funT = I,
  additional_arguments = K [],
  wrap_compilation = K (K (K (K (K I))))
   : (compilation_funs -> string -> typ -> mode -> term list -> term -> term),
  transform_additional_arguments = K I : (indprem -> term list -> term list)
  }

val pos_random_dseq_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = Pos_Random_DSeq,
  function_name_prefix = "random_dseq_",
  compfuns = Random_Sequence_CompFuns.compfuns,
  mk_random = (fn T => fn additional_arguments =>
  let
    val random = Const ("Quickcheck.random_class.random",
      @{typ code_numeral} --> @{typ Random.seed} -->
        HOLogic.mk_prodT (HOLogic.mk_prodT (T, @{typ "unit => term"}), @{typ Random.seed}))
  in
    Const ("Random_Sequence.Random", (@{typ code_numeral} --> @{typ Random.seed} -->
      HOLogic.mk_prodT (HOLogic.mk_prodT (T, @{typ "unit => term"}), @{typ Random.seed})) -->
      Random_Sequence_CompFuns.mk_random_dseqT T) $ random
  end),

  modify_funT = I,
  additional_arguments = K [],
  wrap_compilation = K (K (K (K (K I))))
   : (compilation_funs -> string -> typ -> mode -> term list -> term -> term),
  transform_additional_arguments = K I : (indprem -> term list -> term list)
  }

val neg_random_dseq_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = Neg_Random_DSeq,
  function_name_prefix = "random_dseq_neg_",
  compfuns = Random_Sequence_CompFuns.compfuns,
  mk_random = (fn _ => error "no random generation"),
  modify_funT = I,
  additional_arguments = K [],
  wrap_compilation = K (K (K (K (K I))))
   : (compilation_funs -> string -> typ -> mode -> term list -> term -> term),
  transform_additional_arguments = K I : (indprem -> term list -> term list)
  }


val new_pos_random_dseq_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = New_Pos_Random_DSeq,
  function_name_prefix = "new_random_dseq_",
  compfuns = New_Pos_Random_Sequence_CompFuns.compfuns,
  mk_random = (fn T => fn additional_arguments =>
  let
    val random = Const ("Quickcheck.random_class.random",
      @{typ code_numeral} --> @{typ Random.seed} -->
        HOLogic.mk_prodT (HOLogic.mk_prodT (T, @{typ "unit => term"}), @{typ Random.seed}))
  in
    Const ("New_Random_Sequence.Random", (@{typ code_numeral} --> @{typ Random.seed} -->
      HOLogic.mk_prodT (HOLogic.mk_prodT (T, @{typ "unit => term"}), @{typ Random.seed})) -->
      New_Pos_Random_Sequence_CompFuns.mk_pos_random_dseqT T) $ random
  end),
  modify_funT = I,
  additional_arguments = K [],
  wrap_compilation = K (K (K (K (K I))))
   : (compilation_funs -> string -> typ -> mode -> term list -> term -> term),
  transform_additional_arguments = K I : (indprem -> term list -> term list)
  }

val new_neg_random_dseq_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = New_Neg_Random_DSeq,
  function_name_prefix = "new_random_dseq_neg_",
  compfuns = New_Neg_Random_Sequence_CompFuns.compfuns,
  mk_random = (fn _ => error "no random generation"),
  modify_funT = I,
  additional_arguments = K [],
  wrap_compilation = K (K (K (K (K I))))
   : (compilation_funs -> string -> typ -> mode -> term list -> term -> term),
  transform_additional_arguments = K I : (indprem -> term list -> term list)
  }

fun negative_comp_modifiers_of comp_modifiers =
    (case Comp_Mod.compilation comp_modifiers of
      Pos_Random_DSeq => neg_random_dseq_comp_modifiers
    | Neg_Random_DSeq => pos_random_dseq_comp_modifiers
    | New_Pos_Random_DSeq => new_neg_random_dseq_comp_modifiers
    | New_Neg_Random_DSeq => new_pos_random_dseq_comp_modifiers
    | c => comp_modifiers)

(** mode analysis **)

type mode_analysis_options =
  {use_generators : bool,
  reorder_premises : bool,
  infer_pos_and_neg_modes : bool}

fun is_constrt thy =
  let
    val cnstrs = flat (maps
      (map (fn (_, (Tname, _, cs)) => map (apsnd (rpair Tname o length)) cs) o #descr o snd)
      (Symtab.dest (Datatype.get_all thy)));
    fun check t = (case strip_comb t of
        (Free _, []) => true
      | (Const (s, T), ts) => (case (AList.lookup (op =) cnstrs s, body_type T) of
            (SOME (i, Tname), Type (Tname', _)) =>
              length ts = i andalso Tname = Tname' andalso forall check ts
          | _ => false)
      | _ => false)
  in check end;

(*** check if a type is an equality type (i.e. doesn't contain fun)
  FIXME this is only an approximation ***)
fun is_eqT (Type (s, Ts)) = s <> "fun" andalso forall is_eqT Ts
  | is_eqT _ = true;

fun term_vs tm = fold_aterms (fn Free (x, T) => cons x | _ => I) tm [];
val terms_vs = distinct (op =) o maps term_vs;

(** collect all Frees in a term (with duplicates!) **)
fun term_vTs tm =
  fold_aterms (fn Free xT => cons xT | _ => I) tm [];

fun subsets i j =
  if i <= j then
    let
      fun merge xs [] = xs
        | merge [] ys = ys
        | merge (x::xs) (y::ys) = if length x >= length y then x::merge xs (y::ys)
            else y::merge (x::xs) ys;
      val is = subsets (i+1) j
    in merge (map (fn ks => i::ks) is) is end
  else [[]];

fun print_failed_mode options thy modes p (pol, m) rs is =
  if show_mode_inference options then
    let
      val _ = tracing ("Clauses " ^ commas (map (fn i => string_of_int (i + 1)) is) ^ " of " ^
        p ^ " violates mode " ^ string_of_mode m)
    in () end
  else ()

fun error_of p (pol, m) is =
  "  Clauses " ^ commas (map (fn i => string_of_int (i + 1)) is) ^ " of " ^
        p ^ " violates mode " ^ string_of_mode m

fun is_all_input mode =
  let
    fun is_all_input' (Fun _) = true
      | is_all_input' (Pair (m1, m2)) = is_all_input' m1 andalso is_all_input' m2
      | is_all_input' Input = true
      | is_all_input' Output = false
  in
    forall is_all_input' (strip_fun_mode mode)
  end

fun all_input_of T =
  let
    val (Ts, U) = strip_type T
    fun input_of (Type (@{type_name Product_Type.prod}, [T1, T2])) = Pair (input_of T1, input_of T2)
      | input_of _ = Input
  in
    if U = HOLogic.boolT then
      fold_rev (curry Fun) (map input_of Ts) Bool
    else
      raise Fail "all_input_of: not a predicate"
  end

fun find_least ord xs =
  let
    fun find' x y = (case y of NONE => SOME x | SOME y' => if ord (x, y') = LESS then SOME x else y) 
  in
    fold find' xs NONE
  end
  
fun term_vs tm = fold_aterms (fn Free (x, T) => cons x | _ => I) tm [];
val terms_vs = distinct (op =) o maps term_vs;

fun input_mode T =
  let
    val (Ts, U) = strip_type T
  in
    fold_rev (curry Fun) (map (K Input) Ts) Input
  end

fun output_mode T =
  let
    val (Ts, U) = strip_type T
  in
    fold_rev (curry Fun) (map (K Output) Ts) Output
  end

fun is_invertible_function ctxt (Const (f, _)) = is_constr ctxt f
  | is_invertible_function ctxt _ = false

fun non_invertible_subterms ctxt (t as Free _) = []
  | non_invertible_subterms ctxt t = 
  let
    val (f, args) = strip_comb t
  in
    if is_invertible_function ctxt f then
      maps (non_invertible_subterms ctxt) args
    else
      [t]
  end

fun collect_non_invertible_subterms ctxt (f as Free _) (names, eqs) = (f, (names, eqs))
  | collect_non_invertible_subterms ctxt t (names, eqs) =
    case (strip_comb t) of (f, args) =>
      if is_invertible_function ctxt f then
          let
            val (args', (names', eqs')) =
              fold_map (collect_non_invertible_subterms ctxt) args (names, eqs)
          in
            (list_comb (f, args'), (names', eqs'))
          end
        else
          let
            val s = Name.variant names "x"
            val v = Free (s, fastype_of t)
          in
            (v, (s :: names, HOLogic.mk_eq (v, t) :: eqs))
          end
(*
  if is_constrt thy t then (t, (names, eqs)) else
    let
      val s = Name.variant names "x"
      val v = Free (s, fastype_of t)
    in (v, (s::names, HOLogic.mk_eq (v, t)::eqs)) end;
*)

fun is_possible_output ctxt vs t =
  forall
    (fn t => is_eqT (fastype_of t) andalso forall (member (op =) vs) (term_vs t))
      (non_invertible_subterms ctxt t)
  andalso
    (forall (is_eqT o snd)
      (inter (fn ((f', _), f) => f = f') vs (Term.add_frees t [])))

fun vars_of_destructable_term ctxt (Free (x, _)) = [x]
  | vars_of_destructable_term ctxt t =
  let
    val (f, args) = strip_comb t
  in
    if is_invertible_function ctxt f then
      maps (vars_of_destructable_term ctxt) args
    else
      []
  end

fun is_constructable vs t = forall (member (op =) vs) (term_vs t)

fun missing_vars vs t = subtract (op =) vs (term_vs t)

fun output_terms (Const (@{const_name Pair}, _) $ t1 $ t2, Mode_Pair (d1, d2)) =
    output_terms (t1, d1)  @ output_terms (t2, d2)
  | output_terms (t1 $ t2, Mode_App (d1, d2)) =
    output_terms (t1, d1)  @ output_terms (t2, d2)
  | output_terms (t, Term Output) = [t]
  | output_terms _ = []

fun lookup_mode modes (Const (s, T)) =
   (case (AList.lookup (op =) modes s) of
      SOME ms => SOME (map (fn m => (Context m, [])) ms)
    | NONE => NONE)
  | lookup_mode modes (Free (x, _)) =
    (case (AList.lookup (op =) modes x) of
      SOME ms => SOME (map (fn m => (Context m , [])) ms)
    | NONE => NONE)

fun derivations_of (ctxt : Proof.context) modes vs (Const (@{const_name Pair}, _) $ t1 $ t2) (Pair (m1, m2)) =
    map_product
      (fn (m1, mvars1) => fn (m2, mvars2) => (Mode_Pair (m1, m2), union (op =) mvars1 mvars2))
        (derivations_of ctxt modes vs t1 m1) (derivations_of ctxt modes vs t2 m2)
  | derivations_of ctxt modes vs t (m as Fun _) =
    (*let
      val (p, args) = strip_comb t
    in
      (case lookup_mode modes p of
        SOME ms => map_filter (fn (Context m, []) => let
          val ms = strip_fun_mode m
          val (argms, restms) = chop (length args) ms
          val m' = fold_rev (curry Fun) restms Bool
        in
          if forall (fn m => eq_mode (Input, m)) argms andalso eq_mode (m', mode) then
            SOME (fold (curry Mode_App) (map Term argms) (Context m), missing_vars vs t)
          else NONE
        end) ms
      | NONE => (if is_all_input mode then [(Context mode, [])] else []))
    end*)
    (case try (all_derivations_of ctxt modes vs) t  of
      SOME derivs =>
        filter (fn (d, mvars) => eq_mode (mode_of d, m) andalso null (output_terms (t, d))) derivs
    | NONE => (if is_all_input m then [(Context m, [])] else []))
  | derivations_of ctxt modes vs t m =
    if eq_mode (m, Input) then
      [(Term Input, missing_vars vs t)]
    else if eq_mode (m, Output) then
      (if is_possible_output ctxt vs t then [(Term Output, [])] else [])
    else []
and all_derivations_of ctxt modes vs (Const (@{const_name Pair}, _) $ t1 $ t2) =
  let
    val derivs1 = all_derivations_of ctxt modes vs t1
    val derivs2 = all_derivations_of ctxt modes vs t2
  in
    map_product
      (fn (m1, mvars1) => fn (m2, mvars2) => (Mode_Pair (m1, m2), union (op =) mvars1 mvars2))
        derivs1 derivs2
  end
  | all_derivations_of ctxt modes vs (t1 $ t2) =
  let
    val derivs1 = all_derivations_of ctxt modes vs t1
  in
    maps (fn (d1, mvars1) =>
      case mode_of d1 of
        Fun (m', _) => map (fn (d2, mvars2) =>
          (Mode_App (d1, d2), union (op =) mvars1 mvars2)) (derivations_of ctxt modes vs t2 m')
        | _ => raise Fail "all_derivations_of: derivation has an unexpected non-functional mode") derivs1
  end
  | all_derivations_of _ modes vs (Const (s, T)) = the (lookup_mode modes (Const (s, T)))
  | all_derivations_of _ modes vs (Free (x, T)) = the (lookup_mode modes (Free (x, T)))
  | all_derivations_of _ modes vs _ = raise Fail "all_derivations_of: unexpected term"

fun rev_option_ord ord (NONE, NONE) = EQUAL
  | rev_option_ord ord (NONE, SOME _) = GREATER
  | rev_option_ord ord (SOME _, NONE) = LESS
  | rev_option_ord ord (SOME x, SOME y) = ord (x, y)

fun random_mode_in_deriv modes t deriv =
  case try dest_Const (fst (strip_comb t)) of
    SOME (s, _) =>
      (case AList.lookup (op =) modes s of
        SOME ms =>
          (case AList.lookup (op =) (map (fn ((p, m), r) => (m, r)) ms) (head_mode_of deriv) of
            SOME r => r
          | NONE => false)
      | NONE => false)
  | NONE => false

fun number_of_output_positions mode =
  let
    val args = strip_fun_mode mode
    fun contains_output (Fun _) = false
      | contains_output Input = false
      | contains_output Output = true
      | contains_output (Pair (m1, m2)) = contains_output m1 orelse contains_output m2
  in
    length (filter contains_output args)
  end

fun lex_ord ord1 ord2 (x, x') =
  case ord1 (x, x') of
    EQUAL => ord2 (x, x')
  | ord => ord

fun lexl_ord [] (x, x') = EQUAL
  | lexl_ord (ord :: ords') (x, x') =
    case ord (x, x') of
      EQUAL => lexl_ord ords' (x, x')
    | ord => ord

fun deriv_ord' ctxt pol pred modes t1 t2 ((deriv1, mvars1), (deriv2, mvars2)) =
  let
    (* prefer functional modes if it is a function *)
    fun fun_ord ((t1, deriv1, mvars1), (t2, deriv2, mvars2)) =
      let
        fun is_functional t mode =
          case try (fst o dest_Const o fst o strip_comb) t of
            NONE => false
          | SOME c => is_some (alternative_compilation_of ctxt c mode)
      in
        case (is_functional t1 (head_mode_of deriv1), is_functional t2 (head_mode_of deriv2)) of
          (true, true) => EQUAL
        | (true, false) => LESS
        | (false, true) => GREATER
        | (false, false) => EQUAL
      end
    (* prefer modes without requirement for generating random values *)
    fun mvars_ord ((t1, deriv1, mvars1), (t2, deriv2, mvars2)) =
      int_ord (length mvars1, length mvars2)
    (* prefer non-random modes *)
    fun random_mode_ord ((t1, deriv1, mvars1), (t2, deriv2, mvars2)) =
      int_ord (if random_mode_in_deriv modes t1 deriv1 then 1 else 0,
               if random_mode_in_deriv modes t2 deriv2 then 1 else 0)
    (* prefer modes with more input and less output *)
    fun output_mode_ord ((t1, deriv1, mvars1), (t2, deriv2, mvars2)) =
      int_ord (number_of_output_positions (head_mode_of deriv1),
        number_of_output_positions (head_mode_of deriv2))
    (* prefer recursive calls *)
    fun is_rec_premise t =
      case fst (strip_comb t) of Const (c, T) => c = pred | _ => false
    fun recursive_ord ((t1, deriv1, mvars1), (t2, deriv2, mvars2)) =
      int_ord (if is_rec_premise t1 then 0 else 1,
        if is_rec_premise t2 then 0 else 1)
    val ord = lexl_ord [mvars_ord, fun_ord, random_mode_ord, output_mode_ord, recursive_ord]
  in
    ord ((t1, deriv1, mvars1), (t2, deriv2, mvars2))
  end

fun deriv_ord ctxt pol pred modes t = deriv_ord' ctxt pol pred modes t t

fun premise_ord thy pol pred modes ((prem1, a1), (prem2, a2)) =
  rev_option_ord (deriv_ord' thy pol pred modes (dest_indprem prem1) (dest_indprem prem2)) (a1, a2)

fun print_mode_list modes =
  tracing ("modes: " ^ (commas (map (fn (s, ms) => s ^ ": " ^
    commas (map (fn (m, r) => string_of_mode m ^ (if r then " random " else " not ")) ms)) modes)))

fun select_mode_prem (mode_analysis_options : mode_analysis_options) (ctxt : Proof.context) pred
  pol (modes, (pos_modes, neg_modes)) vs ps =
  let
    fun choose_mode_of_prem (Prem t) =
          find_least (deriv_ord ctxt pol pred modes t) (all_derivations_of ctxt pos_modes vs t)
      | choose_mode_of_prem (Sidecond t) = SOME (Context Bool, missing_vars vs t)
      | choose_mode_of_prem (Negprem t) = find_least (deriv_ord ctxt (not pol) pred modes t)
          (filter (fn (d, missing_vars) => is_all_input (head_mode_of d))
             (all_derivations_of ctxt neg_modes vs t))
      | choose_mode_of_prem p = raise Fail ("choose_mode_of_prem: unexpected premise " ^ string_of_prem ctxt p)
  in
    if #reorder_premises mode_analysis_options then
      find_least (premise_ord ctxt pol pred modes) (ps ~~ map choose_mode_of_prem ps)
    else
      SOME (hd ps, choose_mode_of_prem (hd ps))
  end

fun check_mode_clause' (mode_analysis_options : mode_analysis_options) ctxt pred param_vs (modes :
  (string * ((bool * mode) * bool) list) list) ((pol, mode) : bool * mode) (ts, ps) =
  let
    val vTs = distinct (op =) (fold Term.add_frees (map dest_indprem ps) (fold Term.add_frees ts []))
    val modes' = modes @ (param_vs ~~ map (fn x => [((true, x), false), ((false, x), false)]) (ho_arg_modes_of mode))
    fun retrieve_modes_of_pol pol = map (fn (s, ms) =>
      (s, map_filter (fn ((p, m), r) => if p = pol then SOME m else NONE | _ => NONE) ms))
    val (pos_modes', neg_modes') =
      if #infer_pos_and_neg_modes mode_analysis_options then
        (retrieve_modes_of_pol pol modes', retrieve_modes_of_pol (not pol) modes')
      else
        let
          val modes = map (fn (s, ms) => (s, map (fn ((p, m), r) => m) ms)) modes'
        in (modes, modes) end
    val (in_ts, out_ts) = split_mode mode ts
    val in_vs = union (op =) param_vs (maps (vars_of_destructable_term ctxt) in_ts)
    val out_vs = terms_vs out_ts
    fun known_vs_after p vs = (case p of
        Prem t => union (op =) vs (term_vs t)
      | Sidecond t => union (op =) vs (term_vs t)
      | Negprem t => union (op =) vs (term_vs t)
      | _ => raise Fail "unexpected premise")
    fun check_mode_prems acc_ps rnd vs [] = SOME (acc_ps, vs, rnd)
      | check_mode_prems acc_ps rnd vs ps =
        (case
          (select_mode_prem mode_analysis_options ctxt pred pol (modes', (pos_modes', neg_modes')) vs ps) of
          SOME (p, SOME (deriv, [])) => check_mode_prems ((p, deriv) :: acc_ps) rnd
            (known_vs_after p vs) (filter_out (equal p) ps)
        | SOME (p, SOME (deriv, missing_vars)) =>
          if #use_generators mode_analysis_options andalso pol then
            check_mode_prems ((p, deriv) :: (map
              (fn v => (Generator (v, the (AList.lookup (op =) vTs v)), Term Output))
                (distinct (op =) missing_vars))
                @ acc_ps) true (known_vs_after p vs) (filter_out (equal p) ps)
          else NONE
        | SOME (p, NONE) => NONE
        | NONE => NONE)
  in
    case check_mode_prems [] false in_vs ps of
      NONE => NONE
    | SOME (acc_ps, vs, rnd) =>
      if forall (is_constructable vs) (in_ts @ out_ts) then
        SOME (ts, rev acc_ps, rnd)
      else
        if #use_generators mode_analysis_options andalso pol then
          let
             val generators = map
              (fn v => (Generator (v, the (AList.lookup (op =) vTs v)), Term Output))
                (subtract (op =) vs (terms_vs (in_ts @ out_ts)))
          in
            SOME (ts, rev (generators @ acc_ps), true)
          end
        else
          NONE
  end

datatype result = Success of bool | Error of string

fun check_modes_pred' mode_analysis_options options thy param_vs clauses modes (p, (ms : ((bool * mode) * bool) list)) =
  let
    fun split xs =
      let
        fun split' [] (ys, zs) = (rev ys, rev zs)
          | split' ((m, Error z) :: xs) (ys, zs) = split' xs (ys, z :: zs)
          | split' (((m : bool * mode), Success rnd) :: xs) (ys, zs) = split' xs ((m, rnd) :: ys, zs)
       in
         split' xs ([], [])
       end
    val rs = these (AList.lookup (op =) clauses p)
    fun check_mode m =
      let
        val res = Output.cond_timeit false "work part of check_mode for one mode" (fn _ => 
          map (check_mode_clause' mode_analysis_options thy p param_vs modes m) rs)
      in
        Output.cond_timeit false "aux part of check_mode for one mode" (fn _ => 
        case find_indices is_none res of
          [] => Success (exists (fn SOME (_, _, true) => true | _ => false) res)
        | is => (print_failed_mode options thy modes p m rs is; Error (error_of p m is)))
      end
    val _ = if show_mode_inference options then
        tracing ("checking " ^ string_of_int (length ms) ^ " modes ...")
      else ()
    val res = Output.cond_timeit false "check_mode" (fn _ => map (fn (m, _) => (m, check_mode m)) ms)
    val (ms', errors) = split res
  in
    ((p, (ms' : ((bool * mode) * bool) list)), errors)
  end;

fun get_modes_pred' mode_analysis_options thy param_vs clauses modes (p, ms) =
  let
    val rs = these (AList.lookup (op =) clauses p)
  in
    (p, map (fn (m, rnd) =>
      (m, map
        ((fn (ts, ps, rnd) => (ts, ps)) o the o
          check_mode_clause' mode_analysis_options thy p param_vs modes m) rs)) ms)
  end;

fun fixp f (x : (string * ((bool * mode) * bool) list) list) =
  let val y = f x
  in if x = y then x else fixp f y end;

fun fixp_with_state f (x : (string * ((bool * mode) * bool) list) list, state) =
  let
    val (y, state') = f (x, state)
  in
    if x = y then (y, state') else fixp_with_state f (y, state')
  end

fun string_of_ext_mode ((pol, mode), rnd) =
  string_of_mode mode ^ "(" ^ (if pol then "pos" else "neg") ^ ", "
  ^ (if rnd then "rnd" else "nornd") ^ ")"

fun print_extra_modes options modes =
  if show_mode_inference options then
    tracing ("Modes of inferred predicates: " ^
      cat_lines (map (fn (s, ms) => s ^ ": " ^ commas (map string_of_ext_mode ms)) modes))
  else ()

fun infer_modes mode_analysis_options options (lookup_mode, lookup_neg_mode, needs_random) ctxt
  preds all_modes param_vs clauses =
  let
    fun appair f (x1, x2) (y1, y2) = (f x1 y1, f x2 y2)
    fun add_needs_random s (false, m) = ((false, m), false)
      | add_needs_random s (true, m) = ((true, m), needs_random s m)
    fun add_polarity_and_random_bit s b ms = map (fn m => add_needs_random s (b, m)) ms
    val prednames = map fst preds
    (* extramodes contains all modes of all constants, should we only use the necessary ones
       - what is the impact on performance? *)
    fun predname_of (Prem t) =
        (case try dest_Const (fst (strip_comb t)) of SOME (c, _) => insert (op =) c | NONE => I)
      | predname_of (Negprem t) =
        (case try dest_Const (fst (strip_comb t)) of SOME (c, _) => insert (op =) c | NONE => I)
      | predname_of _ = I
    val relevant_prednames = fold (fn (_, clauses') =>
      fold (fn (_, ps) => fold Term.add_const_names (map dest_indprem ps)) clauses') clauses []
      |> filter_out (fn name => member (op =) prednames name)
    val extra_modes =
      if #infer_pos_and_neg_modes mode_analysis_options then
        let
          val pos_extra_modes =
            map_filter (fn name => Option.map (pair name) (try lookup_mode name))
            relevant_prednames
          val neg_extra_modes =
            map_filter (fn name => Option.map (pair name) (try lookup_neg_mode name))
              relevant_prednames
        in
          map (fn (s, ms) => (s, (add_polarity_and_random_bit s true ms)
                @ add_polarity_and_random_bit s false (the (AList.lookup (op =) neg_extra_modes s))))
            pos_extra_modes
        end
      else
        map (fn (s, ms) => (s, (add_polarity_and_random_bit s true ms)))
          (map_filter (fn name => Option.map (pair name) (try lookup_mode name))
            relevant_prednames)
    val _ = print_extra_modes options extra_modes
    val start_modes =
      if #infer_pos_and_neg_modes mode_analysis_options then
        map (fn (s, ms) => (s, map (fn m => ((true, m), false)) ms @
          (map (fn m => ((false, m), false)) ms))) all_modes
      else
        map (fn (s, ms) => (s, map (fn m => ((true, m), false)) ms)) all_modes
    fun iteration modes = map
      (check_modes_pred' mode_analysis_options options ctxt param_vs clauses
        (modes @ extra_modes)) modes
    val ((modes : (string * ((bool * mode) * bool) list) list), errors) =
      Output.cond_timeit false "Fixpount computation of mode analysis" (fn () =>
      if show_invalid_clauses options then
        fixp_with_state (fn (modes, errors) =>
          let
            val (modes', new_errors) = split_list (iteration modes)
          in (modes', errors @ flat new_errors) end) (start_modes, [])
        else
          (fixp (fn modes => map fst (iteration modes)) start_modes, []))
    val moded_clauses = map (get_modes_pred' mode_analysis_options ctxt param_vs clauses
      (modes @ extra_modes)) modes
    val need_random = fold (fn (s, ms) => if member (op =) (map fst preds) s then
      cons (s, (map_filter (fn ((true, m), true) => SOME m | _ => NONE) ms)) else I)
      modes []
  in
    ((moded_clauses, need_random), errors)
  end;

(* term construction *)

fun mk_v (names, vs) s T = (case AList.lookup (op =) vs s of
      NONE => (Free (s, T), (names, (s, [])::vs))
    | SOME xs =>
        let
          val s' = Name.variant names s;
          val v = Free (s', T)
        in
          (v, (s'::names, AList.update (op =) (s, v::xs) vs))
        end);

fun distinct_v (Free (s, T)) nvs = mk_v nvs s T
  | distinct_v (t $ u) nvs =
      let
        val (t', nvs') = distinct_v t nvs;
        val (u', nvs'') = distinct_v u nvs';
      in (t' $ u', nvs'') end
  | distinct_v x nvs = (x, nvs);


(** specific rpred functions -- move them to the correct place in this file *)
fun mk_Eval_of (P as (Free (f, _)), T) mode =
let
  fun mk_bounds (Type (@{type_name Product_Type.prod}, [T1, T2])) i =
    let
      val (bs2, i') = mk_bounds T2 i 
      val (bs1, i'') = mk_bounds T1 i'
    in
      (HOLogic.pair_const T1 T2 $ bs1 $ bs2, i'' + 1)
    end
    | mk_bounds T i = (Bound i, i + 1)
  fun mk_prod ((t1, T1), (t2, T2)) = (HOLogic.pair_const T1 T2 $ t1 $ t2, HOLogic.mk_prodT (T1, T2))
  fun mk_tuple [] = (HOLogic.unit, HOLogic.unitT)
    | mk_tuple tTs = foldr1 mk_prod tTs;
  fun mk_split_abs (T as Type (@{type_name Product_Type.prod}, [T1, T2])) t = absdummy (T, HOLogic.split_const (T1, T2, @{typ bool}) $ (mk_split_abs T1 (mk_split_abs T2 t)))
    | mk_split_abs T t = absdummy (T, t)
  val args = rev (fst (fold_map mk_bounds (rev (binder_types T)) 0))
  val (inargs, outargs) = split_mode mode args
  val (inTs, outTs) = split_map_modeT (fn _ => fn T => (SOME T, NONE)) mode (binder_types T)
  val inner_term = PredicateCompFuns.mk_Eval (list_comb (P, inargs), fst (mk_tuple (outargs ~~ outTs)))
in
  fold_rev mk_split_abs (binder_types T) inner_term  
end

fun compile_arg compilation_modifiers additional_arguments ctxt param_modes arg = 
  let
    fun map_params (t as Free (f, T)) =
      (case (AList.lookup (op =) param_modes f) of
          SOME mode =>
            let
              val T' = Comp_Mod.funT_of compilation_modifiers mode T
            in
              mk_Eval_of (Free (f, T'), T) mode
            end
        | NONE => t)
      | map_params t = t
  in
    map_aterms map_params arg
  end

fun compile_match compilation_modifiers additional_arguments ctxt param_modes
      eqs eqs' out_ts success_t =
  let
    val compfuns = Comp_Mod.compfuns compilation_modifiers
    val eqs'' = maps mk_eq eqs @ eqs'
    val eqs'' =
      map (compile_arg compilation_modifiers additional_arguments ctxt param_modes) eqs''
    val names = fold Term.add_free_names (success_t :: eqs'' @ out_ts) [];
    val name = Name.variant names "x";
    val name' = Name.variant (name :: names) "y";
    val T = HOLogic.mk_tupleT (map fastype_of out_ts);
    val U = fastype_of success_t;
    val U' = dest_predT compfuns U;
    val v = Free (name, T);
    val v' = Free (name', T);
  in
    lambda v (fst (Datatype.make_case ctxt Datatype_Case.Quiet [] v
      [(HOLogic.mk_tuple out_ts,
        if null eqs'' then success_t
        else Const (@{const_name HOL.If}, HOLogic.boolT --> U --> U --> U) $
          foldr1 HOLogic.mk_conj eqs'' $ success_t $
            mk_bot compfuns U'),
       (v', mk_bot compfuns U')]))
  end;

fun string_of_tderiv ctxt (t, deriv) = 
  (case (t, deriv) of
    (t1 $ t2, Mode_App (deriv1, deriv2)) =>
      string_of_tderiv ctxt (t1, deriv1) ^ " $ " ^ string_of_tderiv ctxt (t2, deriv2)
  | (Const (@{const_name Pair}, _) $ t1 $ t2, Mode_Pair (deriv1, deriv2)) =>
    "(" ^ string_of_tderiv ctxt (t1, deriv1) ^ ", " ^ string_of_tderiv ctxt (t2, deriv2) ^ ")"
  | (t, Term Input) => Syntax.string_of_term ctxt t ^ "[Input]"
  | (t, Term Output) => Syntax.string_of_term ctxt t ^ "[Output]"
  | (t, Context m) => Syntax.string_of_term ctxt t ^ "[" ^ string_of_mode m ^ "]")

fun compile_expr compilation_modifiers ctxt (t, deriv) param_modes additional_arguments =
  let
    val compfuns = Comp_Mod.compfuns compilation_modifiers
    fun expr_of (t, deriv) =
      (case (t, deriv) of
        (t, Term Input) => SOME (compile_arg compilation_modifiers additional_arguments ctxt param_modes t)
      | (t, Term Output) => NONE
      | (Const (name, T), Context mode) =>
        (case alternative_compilation_of ctxt name mode of
          SOME alt_comp => SOME (alt_comp compfuns T)
        | NONE =>
          SOME (Const (function_name_of (Comp_Mod.compilation compilation_modifiers)
            ctxt name mode,
            Comp_Mod.funT_of compilation_modifiers mode T)))
      | (Free (s, T), Context m) =>
        SOME (Free (s, Comp_Mod.funT_of compilation_modifiers m T))
      | (t, Context m) =>
        let
          val bs = map (pair "x") (binder_types (fastype_of t))
          val bounds = map Bound (rev (0 upto (length bs) - 1))
        in SOME (list_abs (bs, mk_if compfuns (list_comb (t, bounds)))) end
      | (Const (@{const_name Pair}, _) $ t1 $ t2, Mode_Pair (d1, d2)) =>
        (case (expr_of (t1, d1), expr_of (t2, d2)) of
          (NONE, NONE) => NONE
        | (NONE, SOME t) => SOME t
        | (SOME t, NONE) => SOME t
        | (SOME t1, SOME t2) => SOME (HOLogic.mk_prod (t1, t2)))
      | (t1 $ t2, Mode_App (deriv1, deriv2)) =>
        (case (expr_of (t1, deriv1), expr_of (t2, deriv2)) of
          (SOME t, NONE) => SOME t
         | (SOME t, SOME u) => SOME (t $ u)
         | _ => error "something went wrong here!"))
  in
    list_comb (the (expr_of (t, deriv)), additional_arguments)
  end

fun compile_clause compilation_modifiers ctxt all_vs param_modes additional_arguments
  inp (in_ts, out_ts) moded_ps =
  let
    val compfuns = Comp_Mod.compfuns compilation_modifiers
    val compile_match = compile_match compilation_modifiers
      additional_arguments ctxt param_modes
    val (in_ts', (all_vs', eqs)) =
      fold_map (collect_non_invertible_subterms ctxt) in_ts (all_vs, []);
    fun compile_prems out_ts' vs names [] =
          let
            val (out_ts'', (names', eqs')) =
              fold_map (collect_non_invertible_subterms ctxt) out_ts' (names, []);
            val (out_ts''', (names'', constr_vs)) = fold_map distinct_v
              out_ts'' (names', map (rpair []) vs);
          in
            compile_match constr_vs (eqs @ eqs') out_ts'''
              (mk_single compfuns (HOLogic.mk_tuple out_ts))
          end
      | compile_prems out_ts vs names ((p, deriv) :: ps) =
          let
            val vs' = distinct (op =) (flat (vs :: map term_vs out_ts));
            val (out_ts', (names', eqs)) =
              fold_map (collect_non_invertible_subterms ctxt) out_ts (names, [])
            val (out_ts'', (names'', constr_vs')) = fold_map distinct_v
              out_ts' ((names', map (rpair []) vs))
            val mode = head_mode_of deriv
            val additional_arguments' =
              Comp_Mod.transform_additional_arguments compilation_modifiers p additional_arguments
            val (compiled_clause, rest) = case p of
               Prem t =>
                 let
                   val u =
                     compile_expr compilation_modifiers ctxt (t, deriv) param_modes additional_arguments'
                   val (_, out_ts''') = split_mode mode (snd (strip_comb t))
                   val rest = compile_prems out_ts''' vs' names'' ps
                 in
                   (u, rest)
                 end
             | Negprem t =>
                 let
                   val neg_compilation_modifiers =
                     negative_comp_modifiers_of compilation_modifiers
                   val u = mk_not compfuns
                     (compile_expr neg_compilation_modifiers ctxt (t, deriv) param_modes additional_arguments')
                   val (_, out_ts''') = split_mode mode (snd (strip_comb t))
                   val rest = compile_prems out_ts''' vs' names'' ps
                 in
                   (u, rest)
                 end
             | Sidecond t =>
                 let
                   val t = compile_arg compilation_modifiers additional_arguments
                     ctxt param_modes t
                   val rest = compile_prems [] vs' names'' ps;
                 in
                   (mk_if compfuns t, rest)
                 end
             | Generator (v, T) =>
                 let
                   val u = Comp_Mod.mk_random compilation_modifiers T additional_arguments
                   val rest = compile_prems [Free (v, T)]  vs' names'' ps;
                 in
                   (u, rest)
                 end
          in
            compile_match constr_vs' eqs out_ts''
              (mk_bind compfuns (compiled_clause, rest))
          end
    val prem_t = compile_prems in_ts' (map fst param_modes) all_vs' moded_ps;
  in
    mk_bind compfuns (mk_single compfuns inp, prem_t)
  end

(* switch detection *)

(** argument position of an inductive predicates and the executable functions **)

type position = int * int list

fun input_positions_pair Input = [[]]
  | input_positions_pair Output = []
  | input_positions_pair (Fun _) = []
  | input_positions_pair (Pair (m1, m2)) =
    map (cons 1) (input_positions_pair m1) @ map (cons 2) (input_positions_pair m2)

fun input_positions_of_mode mode = flat (map_index
   (fn (i, Input) => [(i, [])]
   | (_, Output) => []
   | (_, Fun _) => []
   | (i, m as Pair (m1, m2)) => map (pair i) (input_positions_pair m))
     (Predicate_Compile_Aux.strip_fun_mode mode))

fun argument_position_pair mode [] = []
  | argument_position_pair (Pair (Fun _, m2)) (2 :: is) = argument_position_pair m2 is
  | argument_position_pair (Pair (m1, m2)) (i :: is) =
    (if eq_mode (m1, Output) andalso i = 2 then
      argument_position_pair m2 is
    else if eq_mode (m2, Output) andalso i = 1 then
      argument_position_pair m1 is
    else (i :: argument_position_pair (if i = 1 then m1 else m2) is))

fun argument_position_of mode (i, is) =
  (i - (length (filter (fn Output => true | Fun _ => true | _ => false)
    (List.take (strip_fun_mode mode, i)))),
  argument_position_pair (nth (strip_fun_mode mode) i) is)

fun nth_pair [] t = t
  | nth_pair (1 :: is) (Const (@{const_name Pair}, _) $ t1 $ _) = nth_pair is t1
  | nth_pair (2 :: is) (Const (@{const_name Pair}, _) $ _ $ t2) = nth_pair is t2
  | nth_pair _ _ = raise Fail "unexpected input for nth_tuple"

(** switch detection analysis **)

fun find_switch_test ctxt (i, is) (ts, prems) =
  let
    val t = nth_pair is (nth ts i)
    val T = fastype_of t
  in
    case T of
      TFree _ => NONE
    | Type (Tcon, _) =>
      (case Datatype_Data.get_constrs (ProofContext.theory_of ctxt) Tcon of
        NONE => NONE
      | SOME cs =>
        (case strip_comb t of
          (Var _, []) => NONE
        | (Free _, []) => NONE
        | (Const (c, T), _) => if AList.defined (op =) cs c then SOME (c, T) else NONE))
  end

fun partition_clause ctxt pos moded_clauses =
  let
    fun insert_list eq (key, value) = AList.map_default eq (key, []) (cons value)
    fun find_switch_test' moded_clause (cases, left) =
      case find_switch_test ctxt pos moded_clause of
        SOME (c, T) => (insert_list (op =) ((c, T), moded_clause) cases, left)
      | NONE => (cases, moded_clause :: left)
  in
    fold find_switch_test' moded_clauses ([], [])
  end

datatype switch_tree =
  Atom of moded_clause list | Node of (position * ((string * typ) * switch_tree) list) * switch_tree

fun mk_switch_tree ctxt mode moded_clauses =
  let
    fun select_best_switch moded_clauses input_position best_switch =
      let
        val ord = option_ord (rev_order o int_ord o (pairself (length o snd o snd)))
        val partition = partition_clause ctxt input_position moded_clauses
        val switch = if (length (fst partition) > 1) then SOME (input_position, partition) else NONE
      in
        case ord (switch, best_switch) of LESS => best_switch
          | EQUAL => best_switch | GREATER => switch
      end
    fun detect_switches moded_clauses =
      case fold (select_best_switch moded_clauses) (input_positions_of_mode mode) NONE of
        SOME (best_pos, (switched_on, left_clauses)) =>
          Node ((best_pos, map (apsnd detect_switches) switched_on),
            detect_switches left_clauses)
      | NONE => Atom moded_clauses
  in
    detect_switches moded_clauses
  end

(** compilation of detected switches **)

fun destruct_constructor_pattern (pat, obj) =
  (case strip_comb pat of
    (f as Free _, []) => cons (pat, obj)
  | (Const (c, T), pat_args) =>
    (case strip_comb obj of
      (Const (c', T'), obj_args) =>
        (if c = c' andalso T = T' then
          fold destruct_constructor_pattern (pat_args ~~ obj_args)
        else raise Fail "pattern and object mismatch")
    | _ => raise Fail "unexpected object")
  | _ => raise Fail "unexpected pattern")


fun compile_switch compilation_modifiers ctxt all_vs param_modes additional_arguments mode
  in_ts' outTs switch_tree =
  let
    val compfuns = Comp_Mod.compfuns compilation_modifiers
    val thy = ProofContext.theory_of ctxt
    fun compile_switch_tree _ _ (Atom []) = NONE
      | compile_switch_tree all_vs ctxt_eqs (Atom moded_clauses) =
        let
          val in_ts' = map (Pattern.rewrite_term thy ctxt_eqs []) in_ts'
          fun compile_clause' (ts, moded_ps) =
            let
              val (ts, out_ts) = split_mode mode ts
              val subst = fold destruct_constructor_pattern (in_ts' ~~ ts) []
              val (fsubst, pat') = List.partition (fn (_, Free _) => true | _ => false) subst
              val moded_ps' = (map o apfst o map_indprem)
                (Pattern.rewrite_term thy (map swap fsubst) []) moded_ps
              val inp = HOLogic.mk_tuple (map fst pat')
              val in_ts' = map (Pattern.rewrite_term thy (map swap fsubst) []) (map snd pat')
              val out_ts' = map (Pattern.rewrite_term thy (map swap fsubst) []) out_ts
            in
              compile_clause compilation_modifiers ctxt all_vs param_modes additional_arguments
                inp (in_ts', out_ts') moded_ps'
            end
        in SOME (foldr1 (mk_sup compfuns) (map compile_clause' moded_clauses)) end
    | compile_switch_tree all_vs ctxt_eqs (Node ((position, switched_clauses), left_clauses)) =
      let
        val (i, is) = argument_position_of mode position
        val inp_var = nth_pair is (nth in_ts' i)
        val x = Name.variant all_vs "x"
        val xt = Free (x, fastype_of inp_var)
        fun compile_single_case ((c, T), switched) =
          let
            val Ts = binder_types T
            val argnames = Name.variant_list (x :: all_vs)
              (map (fn i => "c" ^ string_of_int i) (1 upto length Ts))
            val args = map2 (curry Free) argnames Ts
            val pattern = list_comb (Const (c, T), args)
            val ctxt_eqs' = (inp_var, pattern) :: ctxt_eqs
            val compilation = the_default (mk_bot compfuns (HOLogic.mk_tupleT outTs))
              (compile_switch_tree (argnames @ x :: all_vs) ctxt_eqs' switched)
        in
          (pattern, compilation)
        end
        val switch = fst (Datatype.make_case ctxt Datatype_Case.Quiet [] inp_var
          ((map compile_single_case switched_clauses) @
            [(xt, mk_bot compfuns (HOLogic.mk_tupleT outTs))]))
      in
        case compile_switch_tree all_vs ctxt_eqs left_clauses of
          NONE => SOME switch
        | SOME left_comp => SOME (mk_sup compfuns (switch, left_comp))
      end
  in
    compile_switch_tree all_vs [] switch_tree
  end

(* compilation of predicates *)

fun compile_pred options compilation_modifiers ctxt all_vs param_vs s T (pol, mode) moded_cls =
  let
    val compilation_modifiers = if pol then compilation_modifiers else
      negative_comp_modifiers_of compilation_modifiers
    val additional_arguments = Comp_Mod.additional_arguments compilation_modifiers
      (all_vs @ param_vs)
    val compfuns = Comp_Mod.compfuns compilation_modifiers
    fun is_param_type (T as Type ("fun",[_ , T'])) =
      is_some (try (dest_predT compfuns) T) orelse is_param_type T'
      | is_param_type T = is_some (try (dest_predT compfuns) T)
    val (inpTs, outTs) = split_map_modeT (fn m => fn T => (SOME (funT_of compfuns m T), NONE)) mode
      (binder_types T)
    val predT = mk_predT compfuns (HOLogic.mk_tupleT outTs)
    val funT = Comp_Mod.funT_of compilation_modifiers mode T
    val (in_ts, _) = fold_map (fold_map_aterms_prodT (curry HOLogic.mk_prod)
      (fn T => fn (param_vs, names) =>
        if is_param_type T then
          (Free (hd param_vs, T), (tl param_vs, names))
        else
          let
            val new = Name.variant names "x"
          in (Free (new, T), (param_vs, new :: names)) end)) inpTs
        (param_vs, (all_vs @ param_vs))
    val in_ts' = map_filter (map_filter_prod
      (fn t as Free (x, _) => if member (op =) param_vs x then NONE else SOME t | t => SOME t)) in_ts
    val param_modes = param_vs ~~ ho_arg_modes_of mode
    val compilation =
      if detect_switches options then
        the_default (mk_bot compfuns (HOLogic.mk_tupleT outTs))
          (compile_switch compilation_modifiers ctxt all_vs param_modes additional_arguments mode
            in_ts' outTs (mk_switch_tree ctxt mode moded_cls))
      else
        let
          val cl_ts =
            map (fn (ts, moded_prems) => 
              compile_clause compilation_modifiers ctxt all_vs param_modes additional_arguments
                (HOLogic.mk_tuple in_ts') (split_mode mode ts) moded_prems) moded_cls;
        in
          Comp_Mod.wrap_compilation compilation_modifiers compfuns s T mode additional_arguments
            (if null cl_ts then
              mk_bot compfuns (HOLogic.mk_tupleT outTs)
            else
              foldr1 (mk_sup compfuns) cl_ts)
        end
    val fun_const =
      Const (function_name_of (Comp_Mod.compilation compilation_modifiers)
      ctxt s mode, funT)
  in
    HOLogic.mk_Trueprop
      (HOLogic.mk_eq (list_comb (fun_const, in_ts @ additional_arguments), compilation))
  end;

(** special setup for simpset **)
val HOL_basic_ss' = HOL_basic_ss addsimps (@{thms HOL.simp_thms} @ [@{thm Pair_eq}])
  setSolver (mk_solver "all_tac_solver" (fn _ => fn _ => all_tac))
  setSolver (mk_solver "True_solver" (fn _ => rtac @{thm TrueI}))

(* Definition of executable functions and their intro and elim rules *)

fun print_arities arities = tracing ("Arities:\n" ^
  cat_lines (map (fn (s, (ks, k)) => s ^ ": " ^
    space_implode " -> " (map
      (fn NONE => "X" | SOME k' => string_of_int k')
        (ks @ [SOME k]))) arities));

fun split_lambda (x as Free _) t = lambda x t
  | split_lambda (Const (@{const_name Pair}, _) $ t1 $ t2) t =
    HOLogic.mk_split (split_lambda t1 (split_lambda t2 t))
  | split_lambda (Const ("Product_Type.Unity", _)) t = Abs ("x", HOLogic.unitT, t)
  | split_lambda t _ = raise (TERM ("split_lambda", [t]))

fun strip_split_abs (Const (@{const_name prod_case}, _) $ t) = strip_split_abs t
  | strip_split_abs (Abs (_, _, t)) = strip_split_abs t
  | strip_split_abs t = t

fun mk_args is_eval (m as Pair (m1, m2), T as Type (@{type_name Product_Type.prod}, [T1, T2])) names =
    if eq_mode (m, Input) orelse eq_mode (m, Output) then
      let
        val x = Name.variant names "x"
      in
        (Free (x, T), x :: names)
      end
    else
      let
        val (t1, names') = mk_args is_eval (m1, T1) names
        val (t2, names'') = mk_args is_eval (m2, T2) names'
      in
        (HOLogic.mk_prod (t1, t2), names'')
      end
  | mk_args is_eval ((m as Fun _), T) names =
    let
      val funT = funT_of PredicateCompFuns.compfuns m T
      val x = Name.variant names "x"
      val (args, _) = fold_map (mk_args is_eval) (strip_fun_mode m ~~ binder_types T) (x :: names)
      val (inargs, outargs) = split_map_mode (fn _ => fn t => (SOME t, NONE)) m args
      val t = fold_rev split_lambda args (PredicateCompFuns.mk_Eval
        (list_comb (Free (x, funT), inargs), HOLogic.mk_tuple outargs))
    in
      (if is_eval then t else Free (x, funT), x :: names)
    end
  | mk_args is_eval (_, T) names =
    let
      val x = Name.variant names "x"
    in
      (Free (x, T), x :: names)
    end

fun create_intro_elim_rule ctxt mode defthm mode_id funT pred =
  let
    val funtrm = Const (mode_id, funT)
    val Ts = binder_types (fastype_of pred)
    val (args, argnames) = fold_map (mk_args true) (strip_fun_mode mode ~~ Ts) []
    fun strip_eval _ t =
      let
        val t' = strip_split_abs t
        val (r, _) = PredicateCompFuns.dest_Eval t'
      in (SOME (fst (strip_comb r)), NONE) end
    val (inargs, outargs) = split_map_mode strip_eval mode args
    val eval_hoargs = ho_args_of mode args
    val hoargTs = ho_argsT_of mode Ts
    val hoarg_names' =
      Name.variant_list argnames ((map (fn i => "x" ^ string_of_int i)) (1 upto (length hoargTs)))
    val hoargs' = map2 (curry Free) hoarg_names' hoargTs
    val args' = replace_ho_args mode hoargs' args
    val predpropI = HOLogic.mk_Trueprop (list_comb (pred, args'))
    val predpropE = HOLogic.mk_Trueprop (list_comb (pred, args))
    val param_eqs = map2 (HOLogic.mk_Trueprop oo (curry HOLogic.mk_eq)) eval_hoargs hoargs'
    val funpropE = HOLogic.mk_Trueprop (PredicateCompFuns.mk_Eval (list_comb (funtrm, inargs),
                    if null outargs then Free("y", HOLogic.unitT) else HOLogic.mk_tuple outargs))
    val funpropI = HOLogic.mk_Trueprop (PredicateCompFuns.mk_Eval (list_comb (funtrm, inargs),
                     HOLogic.mk_tuple outargs))
    val introtrm = Logic.list_implies (predpropI :: param_eqs, funpropI)
    val simprules = [defthm, @{thm eval_pred},
      @{thm "split_beta"}, @{thm "fst_conv"}, @{thm "snd_conv"}, @{thm pair_collapse}]
    val unfolddef_tac = Simplifier.asm_full_simp_tac (HOL_basic_ss addsimps simprules) 1
    val introthm = Goal.prove ctxt
      (argnames @ hoarg_names' @ ["y"]) [] introtrm (fn _ => unfolddef_tac)
    val P = HOLogic.mk_Trueprop (Free ("P", HOLogic.boolT));
    val elimtrm = Logic.list_implies ([funpropE, Logic.mk_implies (predpropE, P)], P)
    val elimthm = Goal.prove ctxt
      (argnames @ ["y", "P"]) [] elimtrm (fn _ => unfolddef_tac)
    val opt_neg_introthm =
      if is_all_input mode then
        let
          val neg_predpropI = HOLogic.mk_Trueprop (HOLogic.mk_not (list_comb (pred, args')))
          val neg_funpropI =
            HOLogic.mk_Trueprop (PredicateCompFuns.mk_Eval
              (PredicateCompFuns.mk_not (list_comb (funtrm, inargs)), HOLogic.unit))
          val neg_introtrm = Logic.list_implies (neg_predpropI :: param_eqs, neg_funpropI)
          val tac =
            Simplifier.asm_full_simp_tac (HOL_basic_ss addsimps
              (@{thm if_False} :: @{thm Predicate.not_pred_eq} :: simprules)) 1
            THEN rtac @{thm Predicate.singleI} 1
        in SOME (Goal.prove ctxt (argnames @ hoarg_names') []
            neg_introtrm (fn _ => tac))
        end
      else NONE
  in
    ((introthm, elimthm), opt_neg_introthm)
  end

fun create_constname_of_mode options thy prefix name T mode = 
  let
    val system_proposal = prefix ^ (Long_Name.base_name name)
      ^ "_" ^ ascii_string_of_mode mode
    val name = the_default system_proposal (proposed_names options name mode)
  in
    Sign.full_bname thy name
  end;

fun create_definitions options preds (name, modes) thy =
  let
    val compfuns = PredicateCompFuns.compfuns
    val T = AList.lookup (op =) preds name |> the
    fun create_definition mode thy =
      let
        val mode_cname = create_constname_of_mode options thy "" name T mode
        val mode_cbasename = Long_Name.base_name mode_cname
        val funT = funT_of compfuns mode T
        val (args, _) = fold_map (mk_args true) ((strip_fun_mode mode) ~~ (binder_types T)) []
        fun strip_eval m t =
          let
            val t' = strip_split_abs t
            val (r, _) = PredicateCompFuns.dest_Eval t'
          in (SOME (fst (strip_comb r)), NONE) end
        val (inargs, outargs) = split_map_mode strip_eval mode args
        val predterm = fold_rev split_lambda inargs
          (PredicateCompFuns.mk_Enum (split_lambda (HOLogic.mk_tuple outargs)
            (list_comb (Const (name, T), args))))
        val lhs = Const (mode_cname, funT)
        val def = Logic.mk_equals (lhs, predterm)
        val ([definition], thy') = thy |>
          Sign.add_consts_i [(Binding.name mode_cbasename, funT, NoSyn)] |>
          Global_Theory.add_defs false [((Binding.name (mode_cbasename ^ "_def"), def), [])]
        val ctxt' = ProofContext.init_global thy'
        val rules as ((intro, elim), _) =
          create_intro_elim_rule ctxt' mode definition mode_cname funT (Const (name, T))
        in thy'
          |> set_function_name Pred name mode mode_cname
          |> add_predfun_data name mode (definition, rules)
          |> Global_Theory.store_thm (Binding.name (mode_cbasename ^ "I"), intro) |> snd
          |> Global_Theory.store_thm (Binding.name (mode_cbasename ^ "E"), elim)  |> snd
          |> Theory.checkpoint
        end;
  in
    thy |> defined_function_of Pred name |> fold create_definition modes
  end;

fun define_functions comp_modifiers compfuns options preds (name, modes) thy =
  let
    val T = AList.lookup (op =) preds name |> the
    fun create_definition mode thy =
      let
        val function_name_prefix = Comp_Mod.function_name_prefix comp_modifiers
        val mode_cname = create_constname_of_mode options thy function_name_prefix name T mode
        val funT = Comp_Mod.funT_of comp_modifiers mode T
      in
        thy |> Sign.add_consts_i [(Binding.name (Long_Name.base_name mode_cname), funT, NoSyn)]
        |> set_function_name (Comp_Mod.compilation comp_modifiers) name mode mode_cname
      end;
  in
    thy
    |> defined_function_of (Comp_Mod.compilation comp_modifiers) name
    |> fold create_definition modes
  end;

(* Proving equivalence of term *)

fun is_Type (Type _) = true
  | is_Type _ = false

(* returns true if t is an application of an datatype constructor *)
(* which then consequently would be splitted *)
(* else false *)
fun is_constructor thy t =
  if (is_Type (fastype_of t)) then
    (case Datatype.get_info thy ((fst o dest_Type o fastype_of) t) of
      NONE => false
    | SOME info => (let
      val constr_consts = maps (fn (_, (_, _, constrs)) => map fst constrs) (#descr info)
      val (c, _) = strip_comb t
      in (case c of
        Const (name, _) => member (op =) constr_consts name
        | _ => false) end))
  else false

(* MAJOR FIXME:  prove_params should be simple
 - different form of introrule for parameters ? *)

fun prove_param options ctxt nargs t deriv =
  let
    val  (f, args) = strip_comb (Envir.eta_contract t)
    val mode = head_mode_of deriv
    val param_derivations = param_derivations_of deriv
    val ho_args = ho_args_of mode args
    val f_tac = case f of
      Const (name, T) => simp_tac (HOL_basic_ss addsimps 
         [@{thm eval_pred}, predfun_definition_of ctxt name mode,
         @{thm split_eta}, @{thm split_beta}, @{thm fst_conv},
         @{thm snd_conv}, @{thm pair_collapse}, @{thm Product_Type.split_conv}]) 1
    | Free _ =>
      Subgoal.FOCUS_PREMS (fn {context = ctxt, params = params, prems, asms, concl, schematics} =>
        let
          val prems' = maps dest_conjunct_prem (take nargs prems)
        in
          MetaSimplifier.rewrite_goal_tac
            (map (fn th => th RS @{thm sym} RS @{thm eq_reflection}) prems') 1
        end) ctxt 1
    | Abs _ => raise Fail "prove_param: No valid parameter term"
  in
    REPEAT_DETERM (rtac @{thm ext} 1)
    THEN print_tac options "prove_param"
    THEN f_tac 
    THEN print_tac options "after prove_param"
    THEN (REPEAT_DETERM (atac 1))
    THEN (EVERY (map2 (prove_param options ctxt nargs) ho_args param_derivations))
    THEN REPEAT_DETERM (rtac @{thm refl} 1)
  end

fun prove_expr options ctxt nargs (premposition : int) (t, deriv) =
  case strip_comb t of
    (Const (name, T), args) =>
      let
        val mode = head_mode_of deriv
        val introrule = predfun_intro_of ctxt name mode
        val param_derivations = param_derivations_of deriv
        val ho_args = ho_args_of mode args
      in
        print_tac options "before intro rule:"
        THEN rtac introrule 1
        THEN print_tac options "after intro rule"
        (* for the right assumption in first position *)
        THEN rotate_tac premposition 1
        THEN atac 1
        THEN print_tac options "parameter goal"
        (* work with parameter arguments *)
        THEN (EVERY (map2 (prove_param options ctxt nargs) ho_args param_derivations))
        THEN (REPEAT_DETERM (atac 1))
      end
  | (Free _, _) =>
    print_tac options "proving parameter call.."
    THEN Subgoal.FOCUS_PREMS (fn {context = ctxt, params, prems, asms, concl, schematics} =>
        let
          val param_prem = nth prems premposition
          val (param, _) = strip_comb (HOLogic.dest_Trueprop (prop_of param_prem))
          val prems' = maps dest_conjunct_prem (take nargs prems)
          fun param_rewrite prem =
            param = snd (HOLogic.dest_eq (HOLogic.dest_Trueprop (prop_of prem)))
          val SOME rew_eq = find_first param_rewrite prems'
          val param_prem' = MetaSimplifier.rewrite_rule
            (map (fn th => th RS @{thm eq_reflection})
              [rew_eq RS @{thm sym}, @{thm split_beta}, @{thm fst_conv}, @{thm snd_conv}])
            param_prem
        in
          rtac param_prem' 1
        end) ctxt 1
    THEN print_tac options "after prove parameter call"

fun SOLVED tac st = FILTER (fn st' => nprems_of st' = nprems_of st - 1) tac st;

fun SOLVEDALL tac st = FILTER (fn st' => nprems_of st' = 0) tac st

fun check_format ctxt st =
  let
    val concl' = Logic.strip_assums_concl (hd (prems_of st))
    val concl = HOLogic.dest_Trueprop concl'
    val expr = fst (strip_comb (fst (PredicateCompFuns.dest_Eval concl)))
    fun valid_expr (Const (@{const_name Predicate.bind}, _)) = true
      | valid_expr (Const (@{const_name Predicate.single}, _)) = true
      | valid_expr _ = false
  in
    if valid_expr expr then
      ((*tracing "expression is valid";*) Seq.single st)
    else
      ((*tracing "expression is not valid";*) Seq.empty) (*error "check_format: wrong format"*)
  end

fun prove_match options ctxt out_ts =
  let
    val thy = ProofContext.theory_of ctxt
    fun get_case_rewrite t =
      if (is_constructor thy t) then let
        val case_rewrites = (#case_rewrites (Datatype.the_info thy
          ((fst o dest_Type o fastype_of) t)))
        in fold (union Thm.eq_thm) (case_rewrites :: map get_case_rewrite (snd (strip_comb t))) [] end
      else []
    val simprules = insert Thm.eq_thm @{thm "unit.cases"} (insert Thm.eq_thm @{thm "prod.cases"}
      (fold (union Thm.eq_thm) (map get_case_rewrite out_ts) []))
  (* replace TRY by determining if it necessary - are there equations when calling compile match? *)
  in
     (* make this simpset better! *)
    asm_full_simp_tac (HOL_basic_ss' addsimps simprules) 1
    THEN print_tac options "after prove_match:"
    THEN (DETERM (TRY (EqSubst.eqsubst_tac ctxt [0] [@{thm HOL.if_P}] 1
           THEN (REPEAT_DETERM (rtac @{thm conjI} 1 THEN (SOLVED (asm_simp_tac HOL_basic_ss' 1))))
           THEN print_tac options "if condition to be solved:"
           THEN (SOLVED (asm_simp_tac HOL_basic_ss' 1 THEN print_tac options "after if simp; in SOLVED:"))
           THEN check_format thy
           THEN print_tac options "after if simplification - a TRY block")))
    THEN print_tac options "after if simplification"
  end;

(* corresponds to compile_fun -- maybe call that also compile_sidecond? *)

fun prove_sidecond ctxt t =
  let
    fun preds_of t nameTs = case strip_comb t of 
      (f as Const (name, T), args) =>
        if is_registered ctxt name then (name, T) :: nameTs
          else fold preds_of args nameTs
      | _ => nameTs
    val preds = preds_of t []
    val defs = map
      (fn (pred, T) => predfun_definition_of ctxt pred
        (all_input_of T))
        preds
  in 
    simp_tac (HOL_basic_ss addsimps
      (@{thms HOL.simp_thms} @ (@{thm eval_pred} :: defs))) 1 
    (* need better control here! *)
  end

fun prove_clause options ctxt nargs mode (_, clauses) (ts, moded_ps) =
  let
    val (in_ts, clause_out_ts) = split_mode mode ts;
    fun prove_prems out_ts [] =
      (prove_match options ctxt out_ts)
      THEN print_tac options "before simplifying assumptions"
      THEN asm_full_simp_tac HOL_basic_ss' 1
      THEN print_tac options "before single intro rule"
      THEN (rtac (if null clause_out_ts then @{thm singleI_unit} else @{thm singleI}) 1)
    | prove_prems out_ts ((p, deriv) :: ps) =
      let
        val premposition = (find_index (equal p) clauses) + nargs
        val mode = head_mode_of deriv
        val rest_tac =
          rtac @{thm bindI} 1
          THEN (case p of Prem t =>
            let
              val (_, us) = strip_comb t
              val (_, out_ts''') = split_mode mode us
              val rec_tac = prove_prems out_ts''' ps
            in
              print_tac options "before clause:"
              (*THEN asm_simp_tac HOL_basic_ss 1*)
              THEN print_tac options "before prove_expr:"
              THEN prove_expr options ctxt nargs premposition (t, deriv)
              THEN print_tac options "after prove_expr:"
              THEN rec_tac
            end
          | Negprem t =>
            let
              val (t, args) = strip_comb t
              val (_, out_ts''') = split_mode mode args
              val rec_tac = prove_prems out_ts''' ps
              val name = (case strip_comb t of (Const (c, _), _) => SOME c | _ => NONE)
              val neg_intro_rule =
                Option.map (fn name =>
                  the (predfun_neg_intro_of ctxt name mode)) name
              val param_derivations = param_derivations_of deriv
              val params = ho_args_of mode args
            in
              print_tac options "before prove_neg_expr:"
              THEN full_simp_tac (HOL_basic_ss addsimps
                [@{thm split_eta}, @{thm split_beta}, @{thm fst_conv},
                 @{thm snd_conv}, @{thm pair_collapse}, @{thm Product_Type.split_conv}]) 1
              THEN (if (is_some name) then
                  print_tac options "before applying not introduction rule"
                  THEN rotate_tac premposition 1
                  THEN etac (the neg_intro_rule) 1
                  THEN rotate_tac (~premposition) 1
                  THEN print_tac options "after applying not introduction rule"
                  THEN (EVERY (map2 (prove_param options ctxt nargs) params param_derivations))
                  THEN (REPEAT_DETERM (atac 1))
                else
                  rtac @{thm not_predI'} 1
                  (* test: *)
                  THEN dtac @{thm sym} 1
                  THEN asm_full_simp_tac (HOL_basic_ss addsimps [@{thm not_False_eq_True}]) 1)
                  THEN simp_tac (HOL_basic_ss addsimps [@{thm not_False_eq_True}]) 1
              THEN rec_tac
            end
          | Sidecond t =>
           rtac @{thm if_predI} 1
           THEN print_tac options "before sidecond:"
           THEN prove_sidecond ctxt t
           THEN print_tac options "after sidecond:"
           THEN prove_prems [] ps)
      in (prove_match options ctxt out_ts)
          THEN rest_tac
      end;
    val prems_tac = prove_prems in_ts moded_ps
  in
    print_tac options "Proving clause..."
    THEN rtac @{thm bindI} 1
    THEN rtac @{thm singleI} 1
    THEN prems_tac
  end;

fun select_sup 1 1 = []
  | select_sup _ 1 = [rtac @{thm supI1}]
  | select_sup n i = (rtac @{thm supI2})::(select_sup (n - 1) (i - 1));

fun prove_one_direction options ctxt clauses preds pred mode moded_clauses =
  let
    val T = the (AList.lookup (op =) preds pred)
    val nargs = length (binder_types T)
    val pred_case_rule = the_elim_of ctxt pred
  in
    REPEAT_DETERM (CHANGED (rewtac @{thm "split_paired_all"}))
    THEN print_tac options "before applying elim rule"
    THEN etac (predfun_elim_of ctxt pred mode) 1
    THEN etac pred_case_rule 1
    THEN print_tac options "after applying elim rule"
    THEN (EVERY (map
           (fn i => EVERY' (select_sup (length moded_clauses) i) i) 
             (1 upto (length moded_clauses))))
    THEN (EVERY (map2 (prove_clause options ctxt nargs mode) clauses moded_clauses))
    THEN print_tac options "proved one direction"
  end;

(** Proof in the other direction **)

fun prove_match2 options ctxt out_ts =
  let
    val thy = ProofContext.theory_of ctxt
    fun split_term_tac (Free _) = all_tac
      | split_term_tac t =
        if (is_constructor thy t) then
          let
            val info = Datatype.the_info thy ((fst o dest_Type o fastype_of) t)
            val num_of_constrs = length (#case_rewrites info)
            val (_, ts) = strip_comb t
          in
            print_tac options ("Term " ^ (Syntax.string_of_term ctxt t) ^ 
              "splitting with rules \n" ^ Display.string_of_thm ctxt (#split_asm info))
            THEN TRY ((Splitter.split_asm_tac [#split_asm info] 1)
              THEN (print_tac options "after splitting with split_asm rules")
            (* THEN (Simplifier.asm_full_simp_tac HOL_basic_ss 1)
              THEN (DETERM (TRY (etac @{thm Pair_inject} 1)))*)
              THEN (REPEAT_DETERM_N (num_of_constrs - 1)
                (etac @{thm botE} 1 ORELSE etac @{thm botE} 2)))
            THEN (assert_tac (Max_number_of_subgoals 2))
            THEN (EVERY (map split_term_tac ts))
          end
      else all_tac
  in
    split_term_tac (HOLogic.mk_tuple out_ts)
    THEN (DETERM (TRY ((Splitter.split_asm_tac [@{thm "split_if_asm"}] 1)
    THEN (etac @{thm botE} 2))))
  end

(* VERY LARGE SIMILIRATIY to function prove_param 
-- join both functions
*)
(* TODO: remove function *)

fun prove_param2 options ctxt t deriv =
  let
    val (f, args) = strip_comb (Envir.eta_contract t)
    val mode = head_mode_of deriv
    val param_derivations = param_derivations_of deriv
    val ho_args = ho_args_of mode args
    val f_tac = case f of
        Const (name, T) => full_simp_tac (HOL_basic_ss addsimps 
           (@{thm eval_pred}::(predfun_definition_of ctxt name mode)
           :: @{thm "Product_Type.split_conv"}::[])) 1
      | Free _ => all_tac
      | _ => error "prove_param2: illegal parameter term"
  in
    print_tac options "before simplification in prove_args:"
    THEN f_tac
    THEN print_tac options "after simplification in prove_args"
    THEN EVERY (map2 (prove_param2 options ctxt) ho_args param_derivations)
  end

fun prove_expr2 options ctxt (t, deriv) = 
  (case strip_comb t of
      (Const (name, T), args) =>
        let
          val mode = head_mode_of deriv
          val param_derivations = param_derivations_of deriv
          val ho_args = ho_args_of mode args
        in
          etac @{thm bindE} 1
          THEN (REPEAT_DETERM (CHANGED (rewtac @{thm "split_paired_all"})))
          THEN print_tac options "prove_expr2-before"
          THEN etac (predfun_elim_of ctxt name mode) 1
          THEN print_tac options "prove_expr2"
          THEN (EVERY (map2 (prove_param2 options ctxt) ho_args param_derivations))
          THEN print_tac options "finished prove_expr2"
        end
      | _ => etac @{thm bindE} 1)

fun prove_sidecond2 options ctxt t = let
  fun preds_of t nameTs = case strip_comb t of 
    (f as Const (name, T), args) =>
      if is_registered ctxt name then (name, T) :: nameTs
        else fold preds_of args nameTs
    | _ => nameTs
  val preds = preds_of t []
  val defs = map
    (fn (pred, T) => predfun_definition_of ctxt pred 
      (all_input_of T))
      preds
  in
   (* only simplify the one assumption *)
   full_simp_tac (HOL_basic_ss' addsimps @{thm eval_pred} :: defs) 1 
   (* need better control here! *)
   THEN print_tac options "after sidecond2 simplification"
   end
  
fun prove_clause2 options ctxt pred mode (ts, ps) i =
  let
    val pred_intro_rule = nth (intros_of ctxt pred) (i - 1)
    val (in_ts, clause_out_ts) = split_mode mode ts;
    val split_ss = HOL_basic_ss' addsimps [@{thm split_eta}, @{thm split_beta},
      @{thm fst_conv}, @{thm snd_conv}, @{thm pair_collapse}]
    fun prove_prems2 out_ts [] =
      print_tac options "before prove_match2 - last call:"
      THEN prove_match2 options ctxt out_ts
      THEN print_tac options "after prove_match2 - last call:"
      THEN (etac @{thm singleE} 1)
      THEN (REPEAT_DETERM (etac @{thm Pair_inject} 1))
      THEN (asm_full_simp_tac HOL_basic_ss' 1)
      THEN (REPEAT_DETERM (etac @{thm Pair_inject} 1))
      THEN (asm_full_simp_tac HOL_basic_ss' 1)
      THEN SOLVED (print_tac options "state before applying intro rule:"
      THEN (rtac pred_intro_rule
      (* How to handle equality correctly? *)
      THEN_ALL_NEW (K (print_tac options "state before assumption matching")
      THEN' (atac ORELSE' ((CHANGED o asm_full_simp_tac split_ss) THEN' (TRY o atac)))
        THEN' (K (print_tac options "state after pre-simplification:"))
      THEN' (K (print_tac options "state after assumption matching:")))) 1)
    | prove_prems2 out_ts ((p, deriv) :: ps) =
      let
        val mode = head_mode_of deriv
        val rest_tac = (case p of
          Prem t =>
          let
            val (_, us) = strip_comb t
            val (_, out_ts''') = split_mode mode us
            val rec_tac = prove_prems2 out_ts''' ps
          in
            (prove_expr2 options ctxt (t, deriv)) THEN rec_tac
          end
        | Negprem t =>
          let
            val (_, args) = strip_comb t
            val (_, out_ts''') = split_mode mode args
            val rec_tac = prove_prems2 out_ts''' ps
            val name = (case strip_comb t of (Const (c, _), _) => SOME c | _ => NONE)
            val param_derivations = param_derivations_of deriv
            val ho_args = ho_args_of mode args
          in
            print_tac options "before neg prem 2"
            THEN etac @{thm bindE} 1
            THEN (if is_some name then
                full_simp_tac (HOL_basic_ss addsimps
                  [predfun_definition_of ctxt (the name) mode]) 1
                THEN etac @{thm not_predE} 1
                THEN simp_tac (HOL_basic_ss addsimps [@{thm not_False_eq_True}]) 1
                THEN (EVERY (map2 (prove_param2 options ctxt) ho_args param_derivations))
              else
                etac @{thm not_predE'} 1)
            THEN rec_tac
          end 
        | Sidecond t =>
          etac @{thm bindE} 1
          THEN etac @{thm if_predE} 1
          THEN prove_sidecond2 options ctxt t
          THEN prove_prems2 [] ps)
      in print_tac options "before prove_match2:"
         THEN prove_match2 options ctxt out_ts
         THEN print_tac options "after prove_match2:"
         THEN rest_tac
      end;
    val prems_tac = prove_prems2 in_ts ps 
  in
    print_tac options "starting prove_clause2"
    THEN etac @{thm bindE} 1
    THEN (etac @{thm singleE'} 1)
    THEN (TRY (etac @{thm Pair_inject} 1))
    THEN print_tac options "after singleE':"
    THEN prems_tac
  end;
 
fun prove_other_direction options ctxt pred mode moded_clauses =
  let
    fun prove_clause clause i =
      (if i < length moded_clauses then etac @{thm supE} 1 else all_tac)
      THEN (prove_clause2 options ctxt pred mode clause i)
  in
    (DETERM (TRY (rtac @{thm unit.induct} 1)))
     THEN (REPEAT_DETERM (CHANGED (rewtac @{thm split_paired_all})))
     THEN (rtac (predfun_intro_of ctxt pred mode) 1)
     THEN (REPEAT_DETERM (rtac @{thm refl} 2))
     THEN (if null moded_clauses then
         etac @{thm botE} 1
       else EVERY (map2 prove_clause moded_clauses (1 upto (length moded_clauses))))
  end;

(** proof procedure **)

fun prove_pred options thy clauses preds pred (pol, mode) (moded_clauses, compiled_term) =
  let
    val ctxt = ProofContext.init_global thy
    val clauses = case AList.lookup (op =) clauses pred of SOME rs => rs | NONE => []
  in
    Goal.prove ctxt (Term.add_free_names compiled_term []) [] compiled_term
      (if not (skip_proof options) then
        (fn _ =>
        rtac @{thm pred_iffI} 1
        THEN print_tac options "after pred_iffI"
        THEN prove_one_direction options ctxt clauses preds pred mode moded_clauses
        THEN print_tac options "proved one direction"
        THEN prove_other_direction options ctxt pred mode moded_clauses
        THEN print_tac options "proved other direction")
      else (fn _ => Skip_Proof.cheat_tac thy))
  end;

(* composition of mode inference, definition, compilation and proof *)

(** auxillary combinators for table of preds and modes **)

fun map_preds_modes f preds_modes_table =
  map (fn (pred, modes) =>
    (pred, map (fn (mode, value) => (mode, f pred mode value)) modes)) preds_modes_table

fun join_preds_modes table1 table2 =
  map_preds_modes (fn pred => fn mode => fn value =>
    (value, the (AList.lookup (op =) (the (AList.lookup (op =) table2 pred)) mode))) table1

fun maps_modes preds_modes_table =
  map (fn (pred, modes) =>
    (pred, map (fn (mode, value) => value) modes)) preds_modes_table

fun compile_preds options comp_modifiers ctxt all_vs param_vs preds moded_clauses =
  map_preds_modes (fn pred => compile_pred options comp_modifiers ctxt all_vs param_vs pred
      (the (AList.lookup (op =) preds pred))) moded_clauses

fun prove options thy clauses preds moded_clauses compiled_terms =
  map_preds_modes (prove_pred options thy clauses preds)
    (join_preds_modes moded_clauses compiled_terms)

fun prove_by_skip options thy _ _ _ compiled_terms =
  map_preds_modes
    (fn pred => fn mode => fn t => Drule.export_without_context (Skip_Proof.make_thm thy t))
    compiled_terms

(* preparation of introduction rules into special datastructures *)
fun dest_prem ctxt params t =
  (case strip_comb t of
    (v as Free _, ts) => if member (op =) params v then Prem t else Sidecond t
  | (c as Const (@{const_name Not}, _), [t]) => (case dest_prem ctxt params t of
      Prem t => Negprem t
    | Negprem _ => error ("Double negation not allowed in premise: " ^
        Syntax.string_of_term ctxt (c $ t)) 
    | Sidecond t => Sidecond (c $ t))
  | (c as Const (s, _), ts) =>
    if is_registered ctxt s then Prem t else Sidecond t
  | _ => Sidecond t)

fun prepare_intrs options ctxt prednames intros =
  let
    val thy = ProofContext.theory_of ctxt
    val intrs = map prop_of intros
    val preds = map (fn c => Const (c, Sign.the_const_type thy c)) prednames
    val (preds, intrs) = unify_consts thy preds intrs
    val ([preds, intrs], _) = fold_burrow (Variable.import_terms false) [preds, intrs] ctxt
    val preds = map dest_Const preds
    val all_vs = terms_vs intrs
    fun generate_modes s T =
      if member (op =) (no_higher_order_predicate options) s then
        all_smodes_of_typ T
      else
        all_modes_of_typ T
    val all_modes = 
      map (fn (s, T) =>
        (s, case proposed_modes options s of
            SOME ms => check_matches_type ctxt s T ms
          | NONE => generate_modes s T)) preds
    val params =
      case intrs of
        [] =>
          let
            val T = snd (hd preds)
            val paramTs =
              ho_argsT_of_typ (binder_types T)
            val param_names = Name.variant_list [] (map (fn i => "p" ^ string_of_int i)
              (1 upto length paramTs))
          in
            map2 (curry Free) param_names paramTs
          end
      | (intr :: _) =>
        let
          val (p, args) = strip_comb (HOLogic.dest_Trueprop (Logic.strip_imp_concl intr)) 
        in
          ho_args_of_typ (snd (dest_Const p)) args
        end
    val param_vs = map (fst o dest_Free) params
    fun add_clause intr clauses =
      let
        val (Const (name, T), ts) = strip_comb (HOLogic.dest_Trueprop (Logic.strip_imp_concl intr))
        val prems = map (dest_prem ctxt params o HOLogic.dest_Trueprop) (Logic.strip_imp_prems intr)
      in
        AList.update op = (name, these (AList.lookup op = clauses name) @
          [(ts, prems)]) clauses
      end;
    val clauses = fold add_clause intrs []
  in
    (preds, all_vs, param_vs, all_modes, clauses)
  end;

(* sanity check of introduction rules *)
(* TODO: rethink check with new modes *)
(*
fun check_format_of_intro_rule thy intro =
  let
    val concl = Logic.strip_imp_concl (prop_of intro)
    val (p, args) = strip_comb (HOLogic.dest_Trueprop concl)
    val params = fst (chop (nparams_of thy (fst (dest_Const p))) args)
    fun check_arg arg = case HOLogic.strip_tupleT (fastype_of arg) of
      (Ts as _ :: _ :: _) =>
        if length (HOLogic.strip_tuple arg) = length Ts then
          true
        else
          error ("Format of introduction rule is invalid: tuples must be expanded:"
          ^ (Syntax.string_of_term_global thy arg) ^ " in " ^
          (Display.string_of_thm_global thy intro)) 
      | _ => true
    val prems = Logic.strip_imp_prems (prop_of intro)
    fun check_prem (Prem t) = forall check_arg args
      | check_prem (Negprem t) = forall check_arg args
      | check_prem _ = true
  in
    forall check_arg args andalso
    forall (check_prem o dest_prem thy params o HOLogic.dest_Trueprop) prems
  end
*)
(*
fun check_intros_elim_match thy prednames =
  let
    fun check predname =
      let
        val intros = intros_of thy predname
        val elim = the_elim_of thy predname
        val nparams = nparams_of thy predname
        val elim' =
          (Drule.export_without_context o Skip_Proof.make_thm thy)
          (mk_casesrule (ProofContext.init_global thy) nparams intros)
      in
        if not (Thm.equiv_thm (elim, elim')) then
          error "Introduction and elimination rules do not match!"
        else true
      end
  in forall check prednames end
*)

(* create code equation *)

fun add_code_equations ctxt preds result_thmss =
  let
    fun add_code_equation (predname, T) (pred, result_thms) =
      let
        val full_mode = fold_rev (curry Fun) (map (K Input) (binder_types T)) Bool
      in
        if member (op =) (modes_of Pred ctxt predname) full_mode then
          let
            val Ts = binder_types T
            val arg_names = Name.variant_list []
              (map (fn i => "x" ^ string_of_int i) (1 upto length Ts))
            val args = map2 (curry Free) arg_names Ts
            val predfun = Const (function_name_of Pred ctxt predname full_mode,
              Ts ---> PredicateCompFuns.mk_predT @{typ unit})
            val rhs = @{term Predicate.holds} $ (list_comb (predfun, args))
            val eq_term = HOLogic.mk_Trueprop
              (HOLogic.mk_eq (list_comb (Const (predname, T), args), rhs))
            val def = predfun_definition_of ctxt predname full_mode
            val tac = fn _ => Simplifier.simp_tac
              (HOL_basic_ss addsimps [def, @{thm holds_eq}, @{thm eval_pred}]) 1
            val eq = Goal.prove ctxt arg_names [] eq_term tac
          in
            (pred, result_thms @ [eq])
          end
        else
          (pred, result_thms)
      end
  in
    map2 add_code_equation preds result_thmss
  end

(** main function of predicate compiler **)

datatype steps = Steps of
  {
  define_functions : options -> (string * typ) list -> string * (bool * mode) list -> theory -> theory,
  prove : options -> theory -> (string * (term list * indprem list) list) list -> (string * typ) list
    -> moded_clause list pred_mode_table -> term pred_mode_table -> thm pred_mode_table,
  add_code_equations : Proof.context -> (string * typ) list
    -> (string * thm list) list -> (string * thm list) list,
  comp_modifiers : Comp_Mod.comp_modifiers,
  use_generators : bool,
  qname : bstring
  }

fun add_equations_of steps mode_analysis_options options prednames thy =
  let
    fun dest_steps (Steps s) = s
    val compilation = Comp_Mod.compilation (#comp_modifiers (dest_steps steps))
    val ctxt = ProofContext.init_global thy
    val _ = print_step options
      ("Starting predicate compiler (compilation: " ^ string_of_compilation compilation
        ^ ") for predicates " ^ commas prednames ^ "...")
      (*val _ = check_intros_elim_match thy prednames*)
      (*val _ = map (check_format_of_intro_rule thy) (maps (intros_of thy) prednames)*)
    val _ =
      if show_intermediate_results options then
        tracing (commas (map (Display.string_of_thm ctxt) (maps (intros_of ctxt) prednames)))
      else ()
    val (preds, all_vs, param_vs, all_modes, clauses) =
      prepare_intrs options ctxt prednames (maps (intros_of ctxt) prednames)
    val _ = print_step options "Infering modes..."
    val (lookup_mode, lookup_neg_mode, needs_random) = (modes_of compilation ctxt,
      modes_of (negative_compilation_of compilation) ctxt, needs_random ctxt)
    val ((moded_clauses, needs_random), errors) =
      Output.cond_timeit (!Quickcheck.timing) "Infering modes"
      (fn _ => infer_modes mode_analysis_options
        options (lookup_mode, lookup_neg_mode, needs_random) ctxt preds all_modes param_vs clauses)
    val thy' = fold (fn (s, ms) => set_needs_random s ms) needs_random thy
    val modes = map (fn (p, mps) => (p, map fst mps)) moded_clauses
    val _ = check_expected_modes preds options modes
    val _ = check_proposed_modes preds options modes errors
    val _ = print_modes options modes
    val _ = print_step options "Defining executable functions..."
    val thy'' =
      Output.cond_timeit (!Quickcheck.timing) "Defining executable functions..."
      (fn _ => fold (#define_functions (dest_steps steps) options preds) modes thy'
      |> Theory.checkpoint)
    val ctxt'' = ProofContext.init_global thy''
    val _ = print_step options "Compiling equations..."
    val compiled_terms =
      Output.cond_timeit (!Quickcheck.timing) "Compiling equations...." (fn _ =>
        compile_preds options
          (#comp_modifiers (dest_steps steps)) ctxt'' all_vs param_vs preds moded_clauses)
    val _ = print_compiled_terms options ctxt'' compiled_terms
    val _ = print_step options "Proving equations..."
    val result_thms =
      Output.cond_timeit (!Quickcheck.timing) "Proving equations...." (fn _ =>
      #prove (dest_steps steps) options thy'' clauses preds moded_clauses compiled_terms)
    val result_thms' = #add_code_equations (dest_steps steps) ctxt'' preds
      (maps_modes result_thms)
    val qname = #qname (dest_steps steps)
    val attrib = fn thy => Attrib.attribute_i thy (Attrib.internal (K (Thm.declaration_attribute
      (fn thm => Context.mapping (Code.add_eqn thm) I))))
    val thy''' =
      Output.cond_timeit (!Quickcheck.timing) "Setting code equations...." (fn _ =>
      fold (fn (name, result_thms) => fn thy => snd (Global_Theory.add_thmss
      [((Binding.qualify true (Long_Name.base_name name) (Binding.name qname), result_thms),
        [attrib thy ])] thy))
      result_thms' thy'' |> Theory.checkpoint)
  in
    thy'''
  end

fun extend' value_of edges_of key (G, visited) =
  let
    val (G', v) = case try (Graph.get_node G) key of
        SOME v => (G, v)
      | NONE => (Graph.new_node (key, value_of key) G, value_of key)
    val (G'', visited') = fold (extend' value_of edges_of)
      (subtract (op =) visited (edges_of (key, v)))
      (G', key :: visited)
  in
    (fold (Graph.add_edge o (pair key)) (edges_of (key, v)) G'', visited')
  end;

fun extend value_of edges_of key G = fst (extend' value_of edges_of key (G, [])) 
  
fun gen_add_equations steps options names thy =
  let
    fun dest_steps (Steps s) = s
    val defined = defined_functions (Comp_Mod.compilation (#comp_modifiers (dest_steps steps)))
    val ctxt = ProofContext.init_global thy
    val thy' = thy
      |> PredData.map (fold (extend (fetch_pred_data ctxt) (depending_preds_of ctxt)) names)
      |> Theory.checkpoint;
    fun strong_conn_of gr keys =
      Graph.strong_conn (Graph.subgraph (member (op =) (Graph.all_succs gr keys)) gr)
    val scc = strong_conn_of (PredData.get thy') names
    fun preprocess name thy =
      PredData.map (Graph.map_node name (map_pred_data (apfst (fn (rules, preprocessed) =>
        if preprocessed then (rules, preprocessed)
        else
          let
            val (named_intros, SOME elim) = rules
            val named_intros' = map (apsnd (preprocess_intro thy)) named_intros
            val pred = Const (name, Sign.the_const_type thy name)
            val ctxt = ProofContext.init_global thy
            val elim_t = mk_casesrule ctxt pred (map snd named_intros')
            val nparams = (case try (Inductive.the_inductive ctxt) name of
                SOME (_, result) => length (Inductive.params_of (#raw_induct result))
              | NONE => 0)
            val elim' = prove_casesrule ctxt (pred, (elim, 0)) elim_t
          in
            ((named_intros', SOME elim'), true)
          end))))
        thy
    val thy'' = fold preprocess (flat scc) thy'
    val thy''' = fold_rev
      (fn preds => fn thy =>
        if not (forall (defined (ProofContext.init_global thy)) preds) then
          let
            val mode_analysis_options = {use_generators = #use_generators (dest_steps steps),
              reorder_premises =
                not (no_topmost_reordering options andalso not (null (inter (op =) preds names))),
              infer_pos_and_neg_modes = #use_generators (dest_steps steps)}
          in
            add_equations_of steps mode_analysis_options options preds thy
          end
        else thy)
      scc thy'' |> Theory.checkpoint
  in thy''' end

val add_equations = gen_add_equations
  (Steps {
  define_functions =
    fn options => fn preds => fn (s, modes) =>
      create_definitions
      options preds (s, map_filter (fn (true, m) => SOME m | _ => NONE) modes),
  prove = prove,
  add_code_equations = add_code_equations,
  comp_modifiers = predicate_comp_modifiers,
  use_generators = false,
  qname = "equation"})

val add_depth_limited_equations = gen_add_equations
  (Steps {
  define_functions =
    fn options => fn preds => fn (s, modes) =>
    define_functions depth_limited_comp_modifiers PredicateCompFuns.compfuns
    options preds (s, map_filter (fn (true, m) => SOME m | _ => NONE) modes),
  prove = prove_by_skip,
  add_code_equations = K (K I),
  comp_modifiers = depth_limited_comp_modifiers,
  use_generators = false,
  qname = "depth_limited_equation"})

val add_annotated_equations = gen_add_equations
  (Steps {
  define_functions =
    fn options => fn preds => fn (s, modes) =>
      define_functions annotated_comp_modifiers PredicateCompFuns.compfuns options preds
      (s, map_filter (fn (true, m) => SOME m | _ => NONE) modes),
  prove = prove_by_skip,
  add_code_equations = K (K I),
  comp_modifiers = annotated_comp_modifiers,
  use_generators = false,
  qname = "annotated_equation"})

val add_random_equations = gen_add_equations
  (Steps {
  define_functions =
    fn options => fn preds => fn (s, modes) =>
      define_functions random_comp_modifiers PredicateCompFuns.compfuns options preds
      (s, map_filter (fn (true, m) => SOME m | _ => NONE) modes),
  comp_modifiers = random_comp_modifiers,
  prove = prove_by_skip,
  add_code_equations = K (K I),
  use_generators = true,
  qname = "random_equation"})

val add_depth_limited_random_equations = gen_add_equations
  (Steps {
  define_functions =
    fn options => fn preds => fn (s, modes) =>
      define_functions depth_limited_random_comp_modifiers PredicateCompFuns.compfuns options preds
      (s, map_filter (fn (true, m) => SOME m | _ => NONE) modes),
  comp_modifiers = depth_limited_random_comp_modifiers,
  prove = prove_by_skip,
  add_code_equations = K (K I),
  use_generators = true,
  qname = "depth_limited_random_equation"})

val add_dseq_equations = gen_add_equations
  (Steps {
  define_functions =
  fn options => fn preds => fn (s, modes) =>
    define_functions dseq_comp_modifiers DSequence_CompFuns.compfuns
    options preds (s, map_filter (fn (true, m) => SOME m | _ => NONE) modes),
  prove = prove_by_skip,
  add_code_equations = K (K I),
  comp_modifiers = dseq_comp_modifiers,
  use_generators = false,
  qname = "dseq_equation"})

val add_random_dseq_equations = gen_add_equations
  (Steps {
  define_functions =
    fn options => fn preds => fn (s, modes) =>
    let
      val pos_modes = map_filter (fn (true, m) => SOME m | _ => NONE) modes
      val neg_modes = map_filter (fn (false, m) => SOME m | _ => NONE) modes
    in define_functions pos_random_dseq_comp_modifiers Random_Sequence_CompFuns.compfuns
      options preds (s, pos_modes)
      #> define_functions neg_random_dseq_comp_modifiers Random_Sequence_CompFuns.compfuns
      options preds (s, neg_modes)
    end,
  prove = prove_by_skip,
  add_code_equations = K (K I),
  comp_modifiers = pos_random_dseq_comp_modifiers,
  use_generators = true,
  qname = "random_dseq_equation"})

val add_new_random_dseq_equations = gen_add_equations
  (Steps {
  define_functions =
    fn options => fn preds => fn (s, modes) =>
    let
      val pos_modes = map_filter (fn (true, m) => SOME m | _ => NONE) modes
      val neg_modes = map_filter (fn (false, m) => SOME m | _ => NONE) modes
    in define_functions new_pos_random_dseq_comp_modifiers New_Pos_Random_Sequence_CompFuns.compfuns
      options preds (s, pos_modes)
      #> define_functions new_neg_random_dseq_comp_modifiers New_Neg_Random_Sequence_CompFuns.compfuns
      options preds (s, neg_modes)
    end,
  prove = prove_by_skip,
  add_code_equations = K (K I),
  comp_modifiers = new_pos_random_dseq_comp_modifiers,
  use_generators = true,
  qname = "new_random_dseq_equation"})

(** user interface **)

(* code_pred_intro attribute *)

fun attrib' f opt_case_name =
  Thm.declaration_attribute (fn thm => Context.mapping (f (opt_case_name, thm)) I);

val code_pred_intro_attrib = attrib' add_intro NONE;


(*FIXME
- Naming of auxiliary rules necessary?
*)

val setup = PredData.put (Graph.empty) #>
  Attrib.setup @{binding code_pred_intro} (Scan.lift (Scan.option Args.name) >> attrib' add_intro)
    "adding alternative introduction rules for code generation of inductive predicates"

(* TODO: make Theory_Data to Generic_Data & remove duplication of local theory and theory *)
(* FIXME ... this is important to avoid changing the background theory below *)
fun generic_code_pred prep_const options raw_const lthy =
  let
    val thy = ProofContext.theory_of lthy
    val const = prep_const thy raw_const
    val ctxt = ProofContext.init_global thy
    val lthy' = Local_Theory.background_theory (PredData.map
        (extend (fetch_pred_data ctxt) (depending_preds_of ctxt) const)) lthy
    val thy' = ProofContext.theory_of lthy'
    val ctxt' = ProofContext.init_global thy'
    val preds = Graph.all_succs (PredData.get thy') [const] |> filter_out (has_elim ctxt')
    fun mk_cases const =
      let
        val T = Sign.the_const_type thy' const
        val pred = Const (const, T)
        val intros = intros_of ctxt' const
      in mk_casesrule lthy' pred intros end  
    val cases_rules = map mk_cases preds
    val cases =
      map2 (fn pred_name => fn case_rule => Rule_Cases.Case {fixes = [],
        assumes = ("that", tl (Logic.strip_imp_prems case_rule))
          :: (map_filter (fn (fact_name, fact) => Option.map (rpair [fact]) fact_name)
            ((SOME (Long_Name.base_name pred_name ^ ".prems") :: names_of ctxt' pred_name) ~~ Logic.strip_imp_prems case_rule)),
        binds = [], cases = []}) preds cases_rules
    val case_env = map2 (fn p => fn c => (Long_Name.base_name p, SOME c)) preds cases
    val lthy'' = lthy'
      |> fold Variable.auto_fixes cases_rules
      |> ProofContext.add_cases true case_env
    fun after_qed thms goal_ctxt =
      let
        val global_thms = ProofContext.export goal_ctxt
          (ProofContext.init_global (ProofContext.theory_of goal_ctxt)) (map the_single thms)
      in
        goal_ctxt |> Local_Theory.background_theory (fold set_elim global_thms #>
          ((case compilation options of
             Pred => add_equations
           | DSeq => add_dseq_equations
           | Pos_Random_DSeq => add_random_dseq_equations
           | Depth_Limited => add_depth_limited_equations
           | Random => add_random_equations
           | Depth_Limited_Random => add_depth_limited_random_equations
           | New_Pos_Random_DSeq => add_new_random_dseq_equations
           | compilation => error ("Compilation not supported")
           ) options [const]))
      end
  in
    Proof.theorem NONE after_qed (map (single o (rpair [])) cases_rules) lthy''
  end;

val code_pred = generic_code_pred (K I);
val code_pred_cmd = generic_code_pred Code.read_const

(* transformation for code generation *)

structure Pred_Result = Proof_Data (
  type T = unit -> term Predicate.pred
  fun init _ () = error "Pred_Result"
);
val put_pred_result = Pred_Result.put;

structure Pred_Random_Result = Proof_Data (
  type T = unit -> int * int -> term Predicate.pred * (int * int)
  fun init _ () = error "Pred_Random_Result"
);
val put_pred_random_result = Pred_Random_Result.put;

structure Dseq_Result = Proof_Data (
  type T = unit -> term DSequence.dseq
  fun init _ () = error "Dseq_Result"
);
val put_dseq_result = Dseq_Result.put;

structure Dseq_Random_Result = Proof_Data (
  type T = unit -> int -> int -> int * int -> term DSequence.dseq * (int * int)
  fun init _ () = error "Dseq_Random_Result"
);
val put_dseq_random_result = Dseq_Random_Result.put;

structure Lseq_Random_Result = Proof_Data (
  type T = unit -> int -> int -> int * int -> int -> term Lazy_Sequence.lazy_sequence
  fun init _ () = error "Lseq_Random_Result"
);
val put_lseq_random_result = Lseq_Random_Result.put;

structure Lseq_Random_Stats_Result = Proof_Data (
  type T = unit -> int -> int -> int * int -> int -> (term * int) Lazy_Sequence.lazy_sequence
  fun init _ () = error "Lseq_Random_Stats_Result"
);
val put_lseq_random_stats_result = Lseq_Random_Stats_Result.put;

(*FIXME turn this into an LCF-guarded preprocessor for comprehensions*)
fun analyze_compr ctxt compfuns param_user_modes (compilation, arguments) t_compr =
  let
    val all_modes_of = all_modes_of compilation
    val split = case t_compr of (Const (@{const_name Collect}, _) $ t) => t
      | _ => error ("Not a set comprehension: " ^ Syntax.string_of_term ctxt t_compr);
    val (body, Ts, fp) = HOLogic.strip_psplits split;
    val output_names = Name.variant_list (Term.add_free_names body [])
      (map (fn i => "x" ^ string_of_int i) (1 upto length Ts))
    val output_frees = map2 (curry Free) output_names (rev Ts)
    val body = subst_bounds (output_frees, body)
    val T_compr = HOLogic.mk_ptupleT fp Ts
    val output_tuple = HOLogic.mk_ptuple fp T_compr (rev output_frees)
    val (pred as Const (name, T), all_args) =
      case strip_comb body of
        (Const (name, T), all_args) => (Const (name, T), all_args)
      | (head, _) => error ("Not a constant: " ^ Syntax.string_of_term ctxt head)
  in
    if defined_functions compilation ctxt name then
      let
        fun extract_mode (Const (@{const_name Pair}, _) $ t1 $ t2) = Pair (extract_mode t1, extract_mode t2)
          | extract_mode (Free (x, _)) = if member (op =) output_names x then Output else Input
          | extract_mode _ = Input
        val user_mode = fold_rev (curry Fun) (map extract_mode all_args) Bool
        fun valid modes1 modes2 =
          case int_ord (length modes1, length modes2) of
            GREATER => error "Not enough mode annotations"
          | LESS => error "Too many mode annotations"
          | EQUAL => forall (fn (m, NONE) => true | (m, SOME m2) => eq_mode (m, m2))
            (modes1 ~~ modes2)
        fun mode_instance_of (m1, m2) =
          let
            fun instance_of (Fun _, Input) = true
              | instance_of (Input, Input) = true
              | instance_of (Output, Output) = true
              | instance_of (Pair (m1, m2), Pair (m1', m2')) =
                  instance_of  (m1, m1') andalso instance_of (m2, m2')
              | instance_of (Pair (m1, m2), Input) =
                  instance_of (m1, Input) andalso instance_of (m2, Input)
              | instance_of (Pair (m1, m2), Output) =
                  instance_of (m1, Output) andalso instance_of (m2, Output)
              | instance_of (Input, Pair (m1, m2)) =
                  instance_of (Input, m1) andalso instance_of (Input, m2)
              | instance_of (Output, Pair (m1, m2)) =
                  instance_of (Output, m1) andalso instance_of (Output, m2)
              | instance_of _ = false
          in forall instance_of (strip_fun_mode m1 ~~ strip_fun_mode m2) end
        val derivs = all_derivations_of ctxt (all_modes_of ctxt) [] body
          |> filter (fn (d, missing_vars) =>
            let
              val (p_mode :: modes) = collect_context_modes d
            in
              null missing_vars andalso
              mode_instance_of (p_mode, user_mode) andalso
              the_default true (Option.map (valid modes) param_user_modes)
            end)
          |> map fst
        val deriv = case derivs of
            [] => error ("No mode possible for comprehension "
                    ^ Syntax.string_of_term ctxt t_compr)
          | [d] => d
          | d :: _ :: _ => (warning ("Multiple modes possible for comprehension "
                    ^ Syntax.string_of_term ctxt t_compr); d);
        val (_, outargs) = split_mode (head_mode_of deriv) all_args
        val additional_arguments =
          case compilation of
            Pred => []
          | Random => map (HOLogic.mk_number @{typ "code_numeral"}) arguments @
            [@{term "(1, 1) :: code_numeral * code_numeral"}]
          | Annotated => []
          | Depth_Limited => [HOLogic.mk_number @{typ "code_numeral"} (hd arguments)]
          | Depth_Limited_Random => map (HOLogic.mk_number @{typ "code_numeral"}) arguments @
            [@{term "(1, 1) :: code_numeral * code_numeral"}]
          | DSeq => []
          | Pos_Random_DSeq => []
          | New_Pos_Random_DSeq => []
        val comp_modifiers =
          case compilation of
            Pred => predicate_comp_modifiers
          | Random => random_comp_modifiers
          | Depth_Limited => depth_limited_comp_modifiers
          | Depth_Limited_Random => depth_limited_random_comp_modifiers
          (*| Annotated => annotated_comp_modifiers*)
          | DSeq => dseq_comp_modifiers
          | Pos_Random_DSeq => pos_random_dseq_comp_modifiers
          | New_Pos_Random_DSeq => new_pos_random_dseq_comp_modifiers
        val t_pred = compile_expr comp_modifiers ctxt
          (body, deriv) [] additional_arguments;
        val T_pred = dest_predT compfuns (fastype_of t_pred)
        val arrange = split_lambda (HOLogic.mk_tuple outargs) output_tuple
      in
        if null outargs then t_pred else mk_map compfuns T_pred T_compr arrange t_pred
      end
    else
      error "Evaluation with values is not possible because compilation with code_pred was not invoked"
  end

fun eval ctxt stats param_user_modes (options as (compilation, arguments)) k t_compr =
  let
    fun count xs x =
      let
        fun count' i [] = i
          | count' i (x' :: xs) = if x = x' then count' (i + 1) xs else count' i xs
      in count' 0 xs end
    fun accumulate xs = map (fn x => (x, count xs x)) (sort int_ord (distinct (op =) xs))
    val compfuns =
      case compilation of
        Random => PredicateCompFuns.compfuns
      | DSeq => DSequence_CompFuns.compfuns
      | Pos_Random_DSeq => Random_Sequence_CompFuns.compfuns
      | New_Pos_Random_DSeq => New_Pos_Random_Sequence_CompFuns.compfuns
      | _ => PredicateCompFuns.compfuns
    val t = analyze_compr ctxt compfuns param_user_modes options t_compr;
    val T = dest_predT compfuns (fastype_of t);
    val t' =
      if stats andalso compilation = New_Pos_Random_DSeq then
        mk_map compfuns T (HOLogic.mk_prodT (HOLogic.termT, @{typ code_numeral}))
          (absdummy (T, HOLogic.mk_prod (HOLogic.term_of_const T $ Bound 0,
            @{term Code_Numeral.of_nat} $ (HOLogic.size_const T $ Bound 0)))) t
      else
        mk_map compfuns T HOLogic.termT (HOLogic.term_of_const T) t
    val thy = ProofContext.theory_of ctxt
    val (ts, statistics) =
      case compilation of
       (* Random =>
          fst (Predicate.yieldn k
          (Code_Eval.eval NONE ("Predicate_Compile_Core.random_eval_ref", random_eval_ref)
            (fn proc => fn g => fn s => g s |>> Predicate.map proc) thy t' []
            |> Random_Engine.run))*)
        Pos_Random_DSeq =>
          let
            val [nrandom, size, depth] = arguments
          in
            rpair NONE (fst (DSequence.yieldn k
              (Code_Runtime.dynamic_value_strict (Dseq_Random_Result.get, put_dseq_random_result, "Predicate_Compile_Core.put_dseq_random_result")
                thy NONE (fn proc => fn g => fn nrandom => fn size => fn s => g nrandom size s |>> DSequence.map proc)
                  t' [] nrandom size
                |> Random_Engine.run)
              depth true))
          end
      | DSeq =>
          rpair NONE (fst (DSequence.yieldn k
            (Code_Runtime.dynamic_value_strict (Dseq_Result.get, put_dseq_result, "Predicate_Compile_Core.put_dseq_result")
              thy NONE DSequence.map t' []) (the_single arguments) true))
      | New_Pos_Random_DSeq =>
          let
            val [nrandom, size, depth] = arguments
            val seed = Random_Engine.next_seed ()
          in
            if stats then
              apsnd (SOME o accumulate) (split_list
              (fst (Lazy_Sequence.yieldn k
                (Code_Runtime.dynamic_value_strict
                  (Lseq_Random_Stats_Result.get, put_lseq_random_stats_result, "Predicate_Compile_Core.put_lseq_random_stats_result")
                  thy NONE
                  (fn proc => fn g => fn nrandom => fn size => fn s => fn depth => g nrandom size s depth
                    |> Lazy_Sequence.mapa (apfst proc))
                    t' [] nrandom size seed depth))))
            else rpair NONE
              (fst (Lazy_Sequence.yieldn k
                (Code_Runtime.dynamic_value_strict
                  (Lseq_Random_Result.get, put_lseq_random_result, "Predicate_Compile_Core.put_lseq_random_result")
                  thy NONE 
                  (fn proc => fn g => fn nrandom => fn size => fn s => fn depth => g nrandom size s depth
                    |> Lazy_Sequence.mapa proc)
                    t' [] nrandom size seed depth)))
          end
      | _ =>
          rpair NONE (fst (Predicate.yieldn k
            (Code_Runtime.dynamic_value_strict (Pred_Result.get, put_pred_result, "Predicate_Compile_Core.put_pred_result")
              thy NONE Predicate.map t' [])))
  in ((T, ts), statistics) end;

fun values ctxt param_user_modes ((raw_expected, stats), comp_options) k t_compr =
  let
    val ((T, ts), statistics) = eval ctxt stats param_user_modes comp_options k t_compr
    val setT = HOLogic.mk_setT T
    val elems = HOLogic.mk_set T ts
    val cont = Free ("...", setT)
    (* check expected values *)
    val () =
      case raw_expected of
        NONE => ()
      | SOME s =>
        if eq_set (op =) (HOLogic.dest_set (Syntax.read_term ctxt s), ts) then ()
        else
          error ("expected and computed values do not match:\n" ^
            "expected values: " ^ Syntax.string_of_term ctxt (Syntax.read_term ctxt s) ^ "\n" ^
            "computed values: " ^ Syntax.string_of_term ctxt elems ^ "\n")
  in
    (if k = ~1 orelse length ts < k then elems
    else Const (@{const_abbrev Set.union}, setT --> setT --> setT) $ elems $ cont, statistics)
  end;

fun values_cmd print_modes param_user_modes options k raw_t state =
  let
    val ctxt = Toplevel.context_of state
    val t = Syntax.read_term ctxt raw_t
    val (t', stats) = values ctxt param_user_modes options k t
    val ty' = Term.type_of t'
    val ctxt' = Variable.auto_fixes t' ctxt
    val pretty_stat =
      case stats of
          NONE => []
        | SOME xs =>
          let
            val total = fold (curry (op +)) (map snd xs) 0
            fun pretty_entry (s, n) =
              [Pretty.str "size", Pretty.brk 1,
               Pretty.str (string_of_int s), Pretty.str ":", Pretty.brk 1,
               Pretty.str (string_of_int n), Pretty.fbrk]
          in
            [Pretty.fbrk, Pretty.str "Statistics:", Pretty.fbrk,
             Pretty.str "total:", Pretty.brk 1, Pretty.str (string_of_int total), Pretty.fbrk]
             @ maps pretty_entry xs
          end
    val p = Print_Mode.with_modes print_modes (fn () =>
      Pretty.block ([Pretty.quote (Syntax.pretty_term ctxt' t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' ty')]
        @ pretty_stat)) ();
  in Pretty.writeln p end;

end;
