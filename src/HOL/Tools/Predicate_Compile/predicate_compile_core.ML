(*  Title:      HOL/Tools/Predicate_Compile/predicate_compile_core.ML
    Author:     Lukas Bulwahn, TU Muenchen

A compiler from predicates specified by intro/elim rules to equations.
*)

signature PREDICATE_COMPILE_CORE =
sig
  val setup : theory -> theory
  val code_pred : Predicate_Compile_Aux.options -> string -> Proof.context -> Proof.state
  val code_pred_cmd : Predicate_Compile_Aux.options -> string -> Proof.context -> Proof.state
  val values_cmd : string list -> Predicate_Compile_Aux.mode option list option
    -> (string option * (Predicate_Compile_Aux.compilation * int list))
    -> int -> string -> Toplevel.state -> unit
  val register_predicate : (string * thm list * thm) -> theory -> theory
  val register_intros : string * thm list -> theory -> theory
  val is_registered : theory -> string -> bool
  val function_name_of : Predicate_Compile_Aux.compilation -> theory
    -> string -> Predicate_Compile_Aux.mode -> string
  val predfun_intro_of: theory -> string -> Predicate_Compile_Aux.mode -> thm
  val predfun_elim_of: theory -> string -> Predicate_Compile_Aux.mode -> thm
  val all_preds_of : theory -> string list
  val modes_of: Predicate_Compile_Aux.compilation
    -> theory -> string -> Predicate_Compile_Aux.mode list
  val all_modes_of : Predicate_Compile_Aux.compilation
    -> theory -> (string * Predicate_Compile_Aux.mode list) list
  val all_random_modes_of : theory -> (string * Predicate_Compile_Aux.mode list) list
  val intros_of : theory -> string -> thm list
  val add_intro : thm -> theory -> theory
  val set_elim : thm -> theory -> theory
  val preprocess_intro : theory -> thm -> thm
  val print_stored_rules : theory -> unit
  val print_all_modes : Predicate_Compile_Aux.compilation -> theory -> unit
  val mk_casesrule : Proof.context -> term -> thm list -> term
  
  val eval_ref : (unit -> term Predicate.pred) option Unsynchronized.ref
  val random_eval_ref : (unit -> int * int -> term Predicate.pred * (int * int))
    option Unsynchronized.ref
  val dseq_eval_ref : (unit -> term DSequence.dseq) option Unsynchronized.ref
  val random_dseq_eval_ref : (unit -> int -> int -> int * int -> term DSequence.dseq * (int * int))
    option Unsynchronized.ref
  val code_pred_intro_attrib : attribute
  
  (* used by Quickcheck_Generator *) 
  (* temporary for testing of the compilation *)
  
  datatype compilation_funs = CompilationFuns of {
    mk_predT : typ -> typ,
    dest_predT : typ -> typ,
    mk_bot : typ -> term,
    mk_single : term -> term,
    mk_bind : term * term -> term,
    mk_sup : term * term -> term,
    mk_if : term -> term,
    mk_not : term -> term,
    mk_map : typ -> typ -> term -> term -> term
  };
  
  val pred_compfuns : compilation_funs
  val randompred_compfuns : compilation_funs
  val add_equations : Predicate_Compile_Aux.options -> string list -> theory -> theory
  val add_random_dseq_equations : Predicate_Compile_Aux.options -> string list -> theory -> theory
  val mk_tracing : string -> term -> term
end;

structure Predicate_Compile_Core : PREDICATE_COMPILE_CORE =
struct

open Predicate_Compile_Aux;

(** auxiliary **)

(* debug stuff *)

fun print_tac s = Seq.single;

fun print_tac' options s = 
  if show_proof_trace options then Tactical.print_tac s else Seq.single;

fun debug_tac msg = Seq.single; (* (fn st => (Output.tracing msg; Seq.single st)); *)

fun assert b = if not b then error "Assertion failed" else warning "Assertion holds"

datatype assertion = Max_number_of_subgoals of int
fun assert_tac (Max_number_of_subgoals i) st =
  if (nprems_of st <= i) then Seq.single st
  else error ("assert_tac: Numbers of subgoals mismatch at goal state :"
    ^ "\n" ^ Pretty.string_of (Pretty.chunks
      (Goal_Display.pretty_goals_without_context (! Goal_Display.goals_limit) st)));

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
  Type ("*", [Type ("*", [T, @{typ "unit => Code_Evaluation.term"}]) ,@{typ Random.seed}])])) = T
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
        (if m = mode_of d2 then m' else error "mode_of")
      | _ => error "mode_of2")
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

type 'a pred_mode_table = (string * (mode * 'a) list) list

(* book-keeping *)

datatype predfun_data = PredfunData of {
  definition : thm,
  intro : thm,
  elim : thm
};

fun rep_predfun_data (PredfunData data) = data;

fun mk_predfun_data (definition, intro, elim) =
  PredfunData {definition = definition, intro = intro, elim = elim}

datatype pred_data = PredData of {
  intros : thm list,
  elim : thm option,
  function_names : (compilation * (mode * string) list) list,
  predfun_data : (mode * predfun_data) list,
  needs_random : mode list
};

fun rep_pred_data (PredData data) = data;

fun mk_pred_data ((intros, elim), (function_names, predfun_data, needs_random)) =
  PredData {intros = intros, elim = elim,
    function_names = function_names, predfun_data = predfun_data, needs_random = needs_random}

fun map_pred_data f (PredData {intros, elim, function_names, predfun_data, needs_random}) =
  mk_pred_data (f ((intros, elim), (function_names, predfun_data, needs_random)))

fun eq_option eq (NONE, NONE) = true
  | eq_option eq (SOME x, SOME y) = eq (x, y)
  | eq_option eq _ = false

fun eq_pred_data (PredData d1, PredData d2) = 
  eq_list (Thm.eq_thm) (#intros d1, #intros d2) andalso
  eq_option (Thm.eq_thm) (#elim d1, #elim d2)

structure PredData = Theory_Data
(
  type T = pred_data Graph.T;
  val empty = Graph.empty;
  val extend = I;
  val merge = Graph.merge eq_pred_data;
);

(* queries *)

fun lookup_pred_data thy name =
  Option.map rep_pred_data (try (Graph.get_node (PredData.get thy)) name)

fun the_pred_data thy name = case lookup_pred_data thy name
 of NONE => error ("No such predicate " ^ quote name)  
  | SOME data => data;

val is_registered = is_some oo lookup_pred_data

val all_preds_of = Graph.keys o PredData.get

fun intros_of thy = map (Thm.transfer thy) o #intros o the_pred_data thy

fun the_elim_of thy name = case #elim (the_pred_data thy name)
 of NONE => error ("No elimination rule for predicate " ^ quote name)
  | SOME thm => Thm.transfer thy thm 
  
val has_elim = is_some o #elim oo the_pred_data;

fun function_names_of compilation thy name =
  case AList.lookup (op =) (#function_names (the_pred_data thy name)) compilation of
    NONE => error ("No " ^ string_of_compilation compilation
      ^ "functions defined for predicate " ^ quote name)
  | SOME fun_names => fun_names

fun function_name_of compilation thy name mode =
  case AList.lookup (op =) (function_names_of compilation thy name) mode of
    NONE => error ("No " ^ string_of_compilation compilation
      ^ "function defined for mode " ^ string_of_mode mode ^ " of predicate " ^ quote name)
  | SOME function_name => function_name

fun modes_of compilation thy name = map fst (function_names_of compilation thy name)

fun all_modes_of compilation thy =
  map_filter (fn name => Option.map (pair name) (try (modes_of compilation thy) name))
    (all_preds_of thy)

val all_random_modes_of = all_modes_of Random

fun defined_functions compilation thy name =
  AList.defined (op =) (#function_names (the_pred_data thy name)) compilation

fun lookup_predfun_data thy name mode =
  Option.map rep_predfun_data
    (AList.lookup (op =) (#predfun_data (the_pred_data thy name)) mode)

fun the_predfun_data thy name mode =
  case lookup_predfun_data thy name mode of
    NONE => error ("No function defined for mode " ^ string_of_mode mode ^
      " of predicate " ^ name)
  | SOME data => data;

val predfun_definition_of = #definition ooo the_predfun_data

val predfun_intro_of = #intro ooo the_predfun_data

val predfun_elim_of = #elim ooo the_predfun_data

(* diagnostic display functions *)

fun print_modes options thy modes =
  if show_modes options then
    tracing ("Inferred modes:\n" ^
      cat_lines (map (fn (s, ms) => s ^ ": " ^ commas (map
        string_of_mode ms)) modes))
  else ()

fun print_pred_mode_table string_of_entry thy pred_mode_table =
  let
    fun print_mode pred (mode, entry) =  "mode : " ^ string_of_mode mode
      ^ string_of_entry pred mode entry
    fun print_pred (pred, modes) =
      "predicate " ^ pred ^ ": " ^ cat_lines (map (print_mode pred) modes)
    val _ = tracing (cat_lines (map print_pred pred_mode_table))
  in () end;

fun string_of_prem thy (Prem t) =
    (Syntax.string_of_term_global thy t) ^ "(premise)"
  | string_of_prem thy (Negprem t) =
    (Syntax.string_of_term_global thy (HOLogic.mk_not t)) ^ "(negative premise)"
  | string_of_prem thy (Sidecond t) =
    (Syntax.string_of_term_global thy t) ^ "(sidecondition)"
  | string_of_prem thy _ = error "string_of_prem: unexpected input"

fun string_of_clause thy pred (ts, prems) =
  (space_implode " --> "
  (map (string_of_prem thy) prems)) ^ " --> " ^ pred ^ " "
   ^ (space_implode " " (map (Syntax.string_of_term_global thy) ts))

fun print_compiled_terms options thy =
  if show_compilation options then
    print_pred_mode_table (fn _ => fn _ => Syntax.string_of_term_global thy) thy
  else K ()

fun print_stored_rules thy =
  let
    val preds = (Graph.keys o PredData.get) thy
    fun print pred () = let
      val _ = writeln ("predicate: " ^ pred)
      val _ = writeln ("introrules: ")
      val _ = fold (fn thm => fn u => writeln (Display.string_of_thm_global thy thm))
        (rev (intros_of thy pred)) ()
    in
      if (has_elim thy pred) then
        writeln ("elimrule: " ^ Display.string_of_thm_global thy (the_elim_of thy pred))
      else
        writeln ("no elimrule defined")
    end
  in
    fold print preds ()
  end;

fun print_all_modes compilation thy =
  let
    val _ = writeln ("Inferred modes:")
    fun print (pred, modes) u =
      let
        val _ = writeln ("predicate: " ^ pred)
        val _ = writeln ("modes: " ^ (commas (map string_of_mode modes)))
      in u end
  in
    fold print (all_modes_of compilation thy) ()
  end

(* validity checks *)
(* EXPECTED MODE and PROPOSED_MODE are largely the same; define a clear semantics for those! *)

fun check_expected_modes preds options modes =
  case expected_modes options of
    SOME (s, ms) => (case AList.lookup (op =) modes s of
      SOME modes =>
        let
          val modes' = modes
        in
          if not (eq_set eq_mode (ms, modes')) then
            error ("expected modes were not inferred:\n"
            ^ "  inferred modes for " ^ s ^ ": " ^ commas (map string_of_mode modes')  ^ "\n"
            ^ "  expected modes for " ^ s ^ ": " ^ commas (map string_of_mode ms))
          else ()
        end
      | NONE => ())
  | NONE => ()

fun check_proposed_modes preds options modes extra_modes errors =
  case proposed_modes options of
    SOME (s, ms) => (case AList.lookup (op =) modes s of
      SOME inferred_ms =>
        let
          val preds_without_modes = map fst (filter (null o snd) (modes @ extra_modes))
          val modes' = inferred_ms
        in
          if not (eq_set eq_mode (ms, modes')) then
            error ("expected modes were not inferred:\n"
            ^ "  inferred modes for " ^ s ^ ": " ^ commas (map string_of_mode modes')  ^ "\n"
            ^ "  expected modes for " ^ s ^ ": " ^ commas (map string_of_mode ms) ^ "\n"
            ^ "For the following clauses, the following modes could not be inferred: " ^ "\n"
            ^ cat_lines errors ^
            (if not (null preds_without_modes) then
              "\n" ^ "No mode inferred for the predicates " ^ commas preds_without_modes
            else ""))
          else ()
        end
      | NONE => ())
  | NONE => ()

(* importing introduction rules *)

fun unify_consts thy cs intr_ts =
  (let
     val add_term_consts_2 = fold_aterms (fn Const c => insert (op =) c | _ => I);
     fun varify (t, (i, ts)) =
       let val t' = map_types (Logic.incr_tvar (i + 1)) (#2 (Type.varify [] t))
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
    (* TODO: put in a function for this next line! *)
    val paramTs = ho_argsT_of (hd (all_modes_of_typ T)) (binder_types T)
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
      val ho_args = ho_args_of (hd (all_modes_of_typ T)) args
      fun subst_of (pred', pred) =
        let
          val subst = Sign.typ_match thy (fastype_of pred', fastype_of pred) Vartab.empty
        in map (fn (indexname, (s, T)) => ((indexname, s), T)) (Vartab.dest subst) end
      fun instantiate_typ th =
        let
          val (pred', _) = strip_intro_concl th
          val _ = if not (fst (dest_Const pred) = fst (dest_Const pred')) then
            error "Trying to instantiate another predicate" else ()
        in Thm.certify_instantiate (subst_of (pred', pred), []) th end;
      fun instantiate_ho_args th =
        let
          val (_, args') = (strip_comb o HOLogic.dest_Trueprop o Logic.strip_imp_concl o prop_of) th
          val ho_args' = map dest_Var (ho_args_of (hd (all_modes_of_typ T)) args')
        in Thm.certify_instantiate ([], ho_args' ~~ ho_args) th end
      val outp_pred =
        Term_Subst.instantiate (subst_of (inp_pred, pred), []) inp_pred
      val ((_, ths'), ctxt1) =
        Variable.import false (map (instantiate_typ #> instantiate_ho_args) ths) ctxt'
    in
      (((outp_pred, ho_args), th' :: ths'), ctxt1)
    end

(* generation of case rules from user-given introduction rules *)

fun mk_args2 (Type ("*", [T1, T2])) st =
    let
      val (t1, st') = mk_args2 T1 st
      val (t2, st'') = mk_args2 T2 st'
    in
      (HOLogic.mk_prod (t1, t2), st'')
    end
  | mk_args2 (T as Type ("fun", _)) (params, ctxt) = 
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
    end
  | mk_args2 T (params, ctxt) =
    let
      val ([x], ctxt') = Variable.variant_fixes ["x"] ctxt
    in
      (Free (x, T), (params, ctxt'))
    end
  
fun mk_casesrule ctxt pred introrules =
  let
    val (((pred, params), intros_th), ctxt1) = import_intros pred introrules ctxt
    val intros = map prop_of intros_th
    val ([propname], ctxt2) = Variable.variant_fixes ["thesis"] ctxt1
    val prop = HOLogic.mk_Trueprop (Free (propname, HOLogic.boolT))
    val argsT = binder_types (fastype_of pred)
    val (argvs, _) = fold_map mk_args2 argsT (params, ctxt2)
    fun mk_case intro =
      let
        val (_, args) = (strip_comb o HOLogic.dest_Trueprop o Logic.strip_imp_concl) intro
        val prems = Logic.strip_imp_prems intro
        val eqprems = map2 (HOLogic.mk_Trueprop oo (curry HOLogic.mk_eq)) argvs args
        val frees = (fold o fold_aterms)
          (fn t as Free _ =>
              if member (op aconv) params t then I else insert (op aconv) t
           | _ => I) (args @ prems) []
      in fold Logic.all frees (Logic.list_implies (eqprems @ prems, prop)) end
    val assm = HOLogic.mk_Trueprop (list_comb (pred, argvs))
    val cases = map mk_case intros
  in Logic.list_implies (assm :: cases, prop) end;

(** preprocessing rules **)

fun imp_prems_conv cv ct =
  case Thm.term_of ct of
    Const ("==>", _) $ _ $ _ => Conv.combination_conv (Conv.arg_conv cv) (imp_prems_conv cv) ct
  | _ => Conv.all_conv ct

fun Trueprop_conv cv ct =
  case Thm.term_of ct of
    Const ("Trueprop", _) $ _ => Conv.arg_conv cv ct  
  | _ => error "Trueprop_conv"

fun preprocess_intro thy rule =
  Conv.fconv_rule
    (imp_prems_conv
      (Trueprop_conv (Conv.try_conv (Conv.rewr_conv (Thm.symmetric @{thm Predicate.eq_is_eq})))))
    (Thm.transfer thy rule)

fun preprocess_elim thy elimrule =
  let
    fun replace_eqs (Const ("Trueprop", _) $ (Const ("op =", T) $ lhs $ rhs)) =
       HOLogic.mk_Trueprop (Const (@{const_name Predicate.eq}, T) $ lhs $ rhs)
     | replace_eqs t = t
    val ctxt = ProofContext.init thy
    val ((_, [elimrule]), ctxt') = Variable.import false [elimrule] ctxt
    val prems = Thm.prems_of elimrule
    val nargs = length (snd (strip_comb (HOLogic.dest_Trueprop (hd prems))))
    fun preprocess_case t =
      let
       val params = Logic.strip_params t
       val (assums1, assums2) = chop nargs (Logic.strip_assums_hyp t)
       val assums_hyp' = assums1 @ (map replace_eqs assums2)
      in
       list_all (params, Logic.list_implies (assums_hyp', Logic.strip_assums_concl t))
      end
    val cases' = map preprocess_case (tl prems)
    val elimrule' = Logic.list_implies ((hd prems) :: cases', Thm.concl_of elimrule)
    val bigeq = (Thm.symmetric (Conv.implies_concl_conv
      (MetaSimplifier.rewrite true [@{thm Predicate.eq_is_eq}])
        (cterm_of thy elimrule')))
    val tac = (fn _ => Skip_Proof.cheat_tac thy)    
    val eq = Goal.prove ctxt' [] [] (Logic.mk_equals ((Thm.prop_of elimrule), elimrule')) tac
  in
    Thm.equal_elim eq elimrule |> singleton (Variable.export ctxt' ctxt)
  end;

fun expand_tuples_elim th = th

val no_compilation = ([], [], [])

fun fetch_pred_data thy name =
  case try (Inductive.the_inductive (ProofContext.init thy)) name of
    SOME (info as (_, result)) => 
      let
        fun is_intro_of intro =
          let
            val (const, _) = strip_comb (HOLogic.dest_Trueprop (concl_of intro))
          in (fst (dest_Const const) = name) end;      
        val intros =
          (map (expand_tuples thy #> preprocess_intro thy) (filter is_intro_of (#intrs result)))
        val index = find_index (fn s => s = name) (#names (fst info))
        val pre_elim = nth (#elims result) index
        val pred = nth (#preds result) index
        (*val elim = singleton (Inductive_Set.codegen_preproc thy) (preprocess_elim thy nparams 
          (expand_tuples_elim pre_elim))*)
        val elim =
          (Drule.standard o Skip_Proof.make_thm thy)
          (mk_casesrule (ProofContext.init thy) pred intros)
      in
        mk_pred_data ((intros, SOME elim), no_compilation)
      end
  | NONE => error ("No such predicate: " ^ quote name)

fun add_predfun_data name mode data =
  let
    val add = (apsnd o apsnd3) (cons (mode, mk_predfun_data data))
  in PredData.map (Graph.map_node name (map_pred_data add)) end

fun is_inductive_predicate thy name =
  is_some (try (Inductive.the_inductive (ProofContext.init thy)) name)

fun depending_preds_of thy (key, value) =
  let
    val intros = (#intros o rep_pred_data) value
  in
    fold Term.add_const_names (map Thm.prop_of intros) []
      |> filter (fn c => (not (c = key)) andalso
        (is_inductive_predicate thy c orelse is_registered thy c))
  end;

fun add_intro thm thy =
  let
    val (name, T) = dest_Const (fst (strip_intro_concl thm))
    fun cons_intro gr =
     case try (Graph.get_node gr) name of
       SOME pred_data => Graph.map_node name (map_pred_data
         (apfst (fn (intros, elim) => (intros @ [thm], elim)))) gr
     | NONE => Graph.new_node (name, mk_pred_data (([thm], NONE), no_compilation)) gr
  in PredData.map cons_intro thy end

fun set_elim thm =
  let
    val (name, _) = dest_Const (fst 
      (strip_comb (HOLogic.dest_Trueprop (hd (prems_of thm)))))
    fun set (intros, _) = (intros, SOME thm)
  in PredData.map (Graph.map_node name (map_pred_data (apfst set))) end

fun register_predicate (constname, pre_intros, pre_elim) thy =
  let
    val intros = map (preprocess_intro thy) pre_intros
    val elim = preprocess_elim thy pre_elim
  in
    if not (member (op =) (Graph.keys (PredData.get thy)) constname) then
      PredData.map
        (Graph.new_node (constname,
          mk_pred_data ((intros, SOME elim), no_compilation))) thy
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
      (Drule.standard o Skip_Proof.make_thm thy)
      (mk_casesrule (ProofContext.init thy) pred pre_intros)
  in register_predicate (constname, pre_intros, pre_elim) thy end

fun defined_function_of compilation pred =
  let
    val set = (apsnd o apfst3) (cons (compilation, []))
  in
    PredData.map (Graph.map_node pred (map_pred_data set))
  end

fun set_function_name compilation pred mode name =
  let
    val set = (apsnd o apfst3)
      (AList.map_default (op =) (compilation, [(mode, name)]) (cons (mode, name)))
  in
    PredData.map (Graph.map_node pred (map_pred_data set))
  end

fun set_needs_random name modes =
  let
    val set = (apsnd o aptrd3) (K modes)
  in
    PredData.map (Graph.map_node name (map_pred_data set))
  end

(* datastructures and setup for generic compilation *)

datatype compilation_funs = CompilationFuns of {
  mk_predT : typ -> typ,
  dest_predT : typ -> typ,
  mk_bot : typ -> term,
  mk_single : term -> term,
  mk_bind : term * term -> term,
  mk_sup : term * term -> term,
  mk_if : term -> term,
  mk_not : term -> term,
  mk_map : typ -> typ -> term -> term -> term
};

fun mk_predT (CompilationFuns funs) = #mk_predT funs
fun dest_predT (CompilationFuns funs) = #dest_predT funs
fun mk_bot (CompilationFuns funs) = #mk_bot funs
fun mk_single (CompilationFuns funs) = #mk_single funs
fun mk_bind (CompilationFuns funs) = #mk_bind funs
fun mk_sup (CompilationFuns funs) = #mk_sup funs
fun mk_if (CompilationFuns funs) = #mk_if funs
fun mk_not (CompilationFuns funs) = #mk_not funs
fun mk_map (CompilationFuns funs) = #mk_map funs

structure PredicateCompFuns =
struct

fun mk_predT T = Type (@{type_name Predicate.pred}, [T])

fun dest_predT (Type (@{type_name Predicate.pred}, [T])) = T
  | dest_predT T = raise TYPE ("dest_predT", [T], []);

fun mk_bot T = Const (@{const_name Orderings.bot}, mk_predT T);

fun mk_single t =
  let val T = fastype_of t
  in Const(@{const_name Predicate.single}, T --> mk_predT T) $ t end;

fun mk_bind (x, f) =
  let val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (@{const_name Predicate.bind}, fastype_of x --> T --> U) $ x $ f
  end;

val mk_sup = HOLogic.mk_binop @{const_name sup};

fun mk_if cond = Const (@{const_name Predicate.if_pred},
  HOLogic.boolT --> mk_predT HOLogic.unitT) $ cond;

fun mk_not t = let val T = mk_predT HOLogic.unitT
  in Const (@{const_name Predicate.not_pred}, T --> T) $ t end

fun mk_Enum f =
  let val T as Type ("fun", [T', _]) = fastype_of f
  in
    Const (@{const_name Predicate.Pred}, T --> mk_predT T') $ f    
  end;

fun mk_Eval (f, x) =
  let
    val T = fastype_of x
  in
    Const (@{const_name Predicate.eval}, mk_predT T --> T --> HOLogic.boolT) $ f $ x
  end;

fun dest_Eval (Const (@{const_name Predicate.eval}, _) $ f $ x) = (f, x)

fun mk_map T1 T2 tf tp = Const (@{const_name Predicate.map},
  (T1 --> T2) --> mk_predT T1 --> mk_predT T2) $ tf $ tp;

val compfuns = CompilationFuns {mk_predT = mk_predT, dest_predT = dest_predT, mk_bot = mk_bot,
  mk_single = mk_single, mk_bind = mk_bind, mk_sup = mk_sup, mk_if = mk_if, mk_not = mk_not,
  mk_map = mk_map};

end;

structure RandomPredCompFuns =
struct

fun mk_randompredT T =
  @{typ Random.seed} --> HOLogic.mk_prodT (PredicateCompFuns.mk_predT T, @{typ Random.seed})

fun dest_randompredT (Type ("fun", [@{typ Random.seed}, Type (@{type_name "*"},
  [Type (@{type_name "Predicate.pred"}, [T]), @{typ Random.seed}])])) = T
  | dest_randompredT T = raise TYPE ("dest_randompredT", [T], []);

fun mk_bot T = Const(@{const_name Quickcheck.empty}, mk_randompredT T)

fun mk_single t =
  let               
    val T = fastype_of t
  in
    Const (@{const_name Quickcheck.single}, T --> mk_randompredT T) $ t
  end;

fun mk_bind (x, f) =
  let
    val T as (Type ("fun", [_, U])) = fastype_of f
  in
    Const (@{const_name Quickcheck.bind}, fastype_of x --> T --> U) $ x $ f
  end

val mk_sup = HOLogic.mk_binop @{const_name Quickcheck.union}

fun mk_if cond = Const (@{const_name Quickcheck.if_randompred},
  HOLogic.boolT --> mk_randompredT HOLogic.unitT) $ cond;

fun mk_not t = let val T = mk_randompredT HOLogic.unitT
  in Const (@{const_name Quickcheck.not_randompred}, T --> T) $ t end

fun mk_map T1 T2 tf tp = Const (@{const_name Quickcheck.map},
  (T1 --> T2) --> mk_randompredT T1 --> mk_randompredT T2) $ tf $ tp

val compfuns = CompilationFuns {mk_predT = mk_randompredT, dest_predT = dest_randompredT,
    mk_bot = mk_bot, mk_single = mk_single, mk_bind = mk_bind, mk_sup = mk_sup, mk_if = mk_if,
    mk_not = mk_not, mk_map = mk_map};

end;

structure DSequence_CompFuns =
struct

fun mk_dseqT T = Type ("fun", [@{typ code_numeral}, Type ("fun", [@{typ bool},
  Type (@{type_name Option.option}, [Type  ("Lazy_Sequence.lazy_sequence", [T])])])])

fun dest_dseqT (Type ("fun", [@{typ code_numeral}, Type ("fun", [@{typ bool},
  Type (@{type_name Option.option}, [Type ("Lazy_Sequence.lazy_sequence", [T])])])])) = T
  | dest_dseqT T = raise TYPE ("dest_dseqT", [T], []);

fun mk_bot T = Const ("DSequence.empty", mk_dseqT T);

fun mk_single t =
  let val T = fastype_of t
  in Const("DSequence.single", T --> mk_dseqT T) $ t end;

fun mk_bind (x, f) =
  let val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const ("DSequence.bind", fastype_of x --> T --> U) $ x $ f
  end;

val mk_sup = HOLogic.mk_binop "DSequence.union";

fun mk_if cond = Const ("DSequence.if_seq",
  HOLogic.boolT --> mk_dseqT HOLogic.unitT) $ cond;

fun mk_not t = let val T = mk_dseqT HOLogic.unitT
  in Const ("DSequence.not_seq", T --> T) $ t end

fun mk_map T1 T2 tf tp = Const ("DSequence.map",
  (T1 --> T2) --> mk_dseqT T1 --> mk_dseqT T2) $ tf $ tp

val compfuns = CompilationFuns {mk_predT = mk_dseqT, dest_predT = dest_dseqT,
    mk_bot = mk_bot, mk_single = mk_single, mk_bind = mk_bind, mk_sup = mk_sup, mk_if = mk_if,
    mk_not = mk_not, mk_map = mk_map}

end;

structure Random_Sequence_CompFuns =
struct

fun mk_random_dseqT T =
  @{typ code_numeral} --> @{typ code_numeral} --> @{typ Random.seed} -->
    HOLogic.mk_prodT (DSequence_CompFuns.mk_dseqT T, @{typ Random.seed})

fun dest_random_dseqT (Type ("fun", [@{typ code_numeral}, Type ("fun", [@{typ code_numeral},
  Type ("fun", [@{typ Random.seed},
  Type (@{type_name "*"}, [T, @{typ Random.seed}])])])])) = DSequence_CompFuns.dest_dseqT T
  | dest_random_dseqT T = raise TYPE ("dest_random_dseqT", [T], []);

fun mk_bot T = Const ("Random_Sequence.empty", mk_random_dseqT T);

fun mk_single t =
  let val T = fastype_of t
  in Const("Random_Sequence.single", T --> mk_random_dseqT T) $ t end;

fun mk_bind (x, f) =
  let
    val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const ("Random_Sequence.bind", fastype_of x --> T --> U) $ x $ f
  end;

val mk_sup = HOLogic.mk_binop "Random_Sequence.union";

fun mk_if cond = Const ("Random_Sequence.if_random_dseq",
  HOLogic.boolT --> mk_random_dseqT HOLogic.unitT) $ cond;

fun mk_not t = let val T = mk_random_dseqT HOLogic.unitT
  in Const ("Random_Sequence.not_random_dseq", T --> T) $ t end

fun mk_map T1 T2 tf tp = Const ("Random_Sequence.map",
  (T1 --> T2) --> mk_random_dseqT T1 --> mk_random_dseqT T2) $ tf $ tp

val compfuns = CompilationFuns {mk_predT = mk_random_dseqT, dest_predT = dest_random_dseqT,
    mk_bot = mk_bot, mk_single = mk_single, mk_bind = mk_bind, mk_sup = mk_sup, mk_if = mk_if,
    mk_not = mk_not, mk_map = mk_map}

end;



fun mk_random T =
  let
    val random = Const ("Quickcheck.random_class.random",
      @{typ code_numeral} --> @{typ Random.seed} -->
        HOLogic.mk_prodT (HOLogic.mk_prodT (T, @{typ "unit => term"}), @{typ Random.seed}))
  in
    Const ("Random_Sequence.Random", (@{typ code_numeral} --> @{typ Random.seed} -->
      HOLogic.mk_prodT (HOLogic.mk_prodT (T, @{typ "unit => term"}), @{typ Random.seed})) -->
      Random_Sequence_CompFuns.mk_random_dseqT T) $ random
  end;



(* for external use with interactive mode *)
val pred_compfuns = PredicateCompFuns.compfuns
val randompred_compfuns = Random_Sequence_CompFuns.compfuns;

(* function types and names of different compilations *)

fun funT_of compfuns mode T =
  let
    val Ts = binder_types T
    val (inTs, outTs) = split_map_modeT (fn m => fn T => (SOME (funT_of compfuns m T), NONE)) mode Ts
  in
    inTs ---> (mk_predT compfuns (HOLogic.mk_tupleT outTs))
  end;

(** mode analysis **)

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

fun print_failed_mode options thy modes p m rs is =
  if show_mode_inference options then
    let
      val _ = tracing ("Clauses " ^ commas (map (fn i => string_of_int (i + 1)) is) ^ " of " ^
        p ^ " violates mode " ^ string_of_mode m)
    in () end
  else ()

fun error_of p m is =
  ("  Clauses " ^ commas (map (fn i => string_of_int (i + 1)) is) ^ " of " ^
        p ^ " violates mode " ^ string_of_mode m)

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
    fun input_of (Type ("*", [T1, T2])) = Pair (input_of T1, input_of T2)
      | input_of _ = Input
  in
    if U = HOLogic.boolT then
      fold_rev (curry Fun) (map input_of Ts) Bool
    else
      error "all_input_of: not a predicate"
  end

fun partial_hd [] = NONE
  | partial_hd (x :: xs) = SOME x

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

fun is_invertible_function thy (Const (f, _)) = is_constr thy f
  | is_invertible_function thy _ = false

fun non_invertible_subterms thy (Free _) = []
  | non_invertible_subterms thy t = 
  case (strip_comb t) of (f, args) =>
    if is_invertible_function thy f then
      maps (non_invertible_subterms thy) args
    else
      [t]

fun collect_non_invertible_subterms thy (f as Free _) (names, eqs) = (f, (names, eqs))
  | collect_non_invertible_subterms thy t (names, eqs) =
    case (strip_comb t) of (f, args) =>
      if is_invertible_function thy f then
          let
            val (args', (names', eqs')) =
              fold_map (collect_non_invertible_subterms thy) args (names, eqs)
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

fun is_possible_output thy vs t =
  forall
    (fn t => is_eqT (fastype_of t) andalso forall (member (op =) vs) (term_vs t))
      (non_invertible_subterms thy t)

fun vars_of_destructable_term thy (Free (x, _)) = [x]
  | vars_of_destructable_term thy t =
  case (strip_comb t) of (f, args) =>
    if is_invertible_function thy f then
      maps (vars_of_destructable_term thy) args
    else
      []

fun is_constructable thy vs t = forall (member (op =) vs) (term_vs t)

fun missing_vars vs t = subtract (op =) vs (term_vs t)

fun derivations_of thy modes vs t Input = 
    [(Term Input, missing_vars vs t)]
  | derivations_of thy modes vs t Output =
    if is_possible_output thy vs t then [(Term Output, [])] else []
  | derivations_of thy modes vs (Const ("Pair", _) $ t1 $ t2) (Pair (m1, m2)) =
    map_product
      (fn (m1, mvars1) => fn (m2, mvars2) => (Mode_Pair (m1, m2), union (op =) mvars1 mvars2))
        (derivations_of thy modes vs t1 m1) (derivations_of thy modes vs t2 m2)
  | derivations_of thy modes vs t m =
    (case try (all_derivations_of thy modes vs) t of
      SOME derivs => filter (fn (d, mvars) => mode_of d = m) derivs
    | NONE => (if is_all_input m then [(Context m, [])] else []))
and all_derivations_of thy modes vs (Const ("Pair", _) $ t1 $ t2) =
  let
    val derivs1 = all_derivations_of thy modes vs t1
    val derivs2 = all_derivations_of thy modes vs t2
  in
    map_product
      (fn (m1, mvars1) => fn (m2, mvars2) => (Mode_Pair (m1, m2), union (op =) mvars1 mvars2))
        derivs1 derivs2
  end
  | all_derivations_of thy modes vs (t1 $ t2) =
  let
    val derivs1 = all_derivations_of thy modes vs t1
  in
    maps (fn (d1, mvars1) =>
      case mode_of d1 of
        Fun (m', _) => map (fn (d2, mvars2) =>
          (Mode_App (d1, d2), union (op =) mvars1 mvars2)) (derivations_of thy modes vs t2 m')
        | _ => error "Something went wrong") derivs1
  end
  | all_derivations_of thy modes vs (Const (s, T)) =
    (case (AList.lookup (op =) modes s) of
      SOME ms => map (fn m => (Context m, [])) ms
    | NONE => error ("No mode for constant " ^ s))
  | all_derivations_of _ modes vs (Free (x, _)) =
    (case (AList.lookup (op =) modes x) of
      SOME ms => map (fn m => (Context m , [])) ms
    | NONE => error ("No mode for parameter variable " ^ x))
  | all_derivations_of _ modes vs _ = error "all_derivations_of"

fun rev_option_ord ord (NONE, NONE) = EQUAL
  | rev_option_ord ord (NONE, SOME _) = GREATER
  | rev_option_ord ord (SOME _, NONE) = LESS
  | rev_option_ord ord (SOME x, SOME y) = ord (x, y)

fun term_of_prem (Prem t) = t
  | term_of_prem (Negprem t) = t
  | term_of_prem (Sidecond t) = t

fun random_mode_in_deriv modes t deriv =
  case try dest_Const (fst (strip_comb t)) of
    SOME (s, _) =>
      (case AList.lookup (op =) modes s of
        SOME ms =>
          (case AList.lookup (op =) ms (head_mode_of deriv) of
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

fun deriv_ord2' thy modes t1 t2 ((deriv1, mvars1), (deriv2, mvars2)) =
  let
    fun mvars_ord ((t1, deriv1, mvars1), (t2, deriv2, mvars2)) =
      int_ord (length mvars1, length mvars2)
    fun random_mode_ord ((t1, deriv1, mvars1), (t2, deriv2, mvars2)) =
      int_ord (if random_mode_in_deriv modes t1 deriv1 then 1 else 0,
        if random_mode_in_deriv modes t1 deriv1 then 1 else 0)
    fun output_mode_ord ((t1, deriv1, mvars1), (t2, deriv2, mvars2)) =
      int_ord (number_of_output_positions (head_mode_of deriv1),
        number_of_output_positions (head_mode_of deriv2))
  in
    lex_ord mvars_ord (lex_ord random_mode_ord output_mode_ord)
      ((t1, deriv1, mvars1), (t2, deriv2, mvars2))
  end

fun deriv_ord2 thy modes t = deriv_ord2' thy modes t t

fun deriv_ord ((deriv1, mvars1), (deriv2, mvars2)) =
  int_ord (length mvars1, length mvars2)

fun premise_ord thy modes ((prem1, a1), (prem2, a2)) =
  rev_option_ord (deriv_ord2' thy modes (term_of_prem prem1) (term_of_prem prem2)) (a1, a2)

fun print_mode_list modes =
  tracing ("modes: " ^ (commas (map (fn (s, ms) => s ^ ": " ^
    commas (map (fn (m, r) => string_of_mode m ^ (if r then " random " else " not ")) ms)) modes)))

fun select_mode_prem' thy modes vs ps =
  let
    val modes' = map (fn (s, ms) => (s, map fst ms)) modes
  in
    partial_hd (sort (premise_ord thy modes) (ps ~~ map
    (fn Prem t =>
      partial_hd
        (sort (deriv_ord2 thy modes t) (all_derivations_of thy modes' vs t))
     | Sidecond t => SOME (Context Bool, missing_vars vs t)
     | Negprem t =>
         partial_hd
          (sort (deriv_ord2 thy modes t) (filter (fn (d, missing_vars) => is_all_input (head_mode_of d))
             (all_derivations_of thy modes' vs t)))
     | p => error (string_of_prem thy p))
    ps))
  end

fun check_mode_clause' use_random thy param_vs modes mode (ts, ps) =
  let
    val vTs = distinct (op =) (fold Term.add_frees (map term_of_prem ps) (fold Term.add_frees ts []))
    val modes' = modes @ (param_vs ~~ map (fn x => [(x, false)]) (ho_arg_modes_of mode))
    val (in_ts, out_ts) = split_mode mode ts    
    val in_vs = maps (vars_of_destructable_term thy) in_ts
    val out_vs = terms_vs out_ts
    fun check_mode_prems acc_ps rnd vs [] = SOME (acc_ps, vs, rnd)
      | check_mode_prems acc_ps rnd vs ps =
        (case select_mode_prem' thy modes' vs ps of
          SOME (p, SOME (deriv, [])) => check_mode_prems ((p, deriv) :: acc_ps) rnd (*TODO: uses random? *)
            (case p of
                Prem t => union (op =) vs (term_vs t)
              | Sidecond t => vs
              | Negprem t => union (op =) vs (term_vs t)
              | _ => error "I do not know")
            (filter_out (equal p) ps)
        | SOME (p, SOME (deriv, missing_vars)) =>
          if use_random then
            check_mode_prems ((p, deriv) :: (map
              (fn v => (Generator (v, the (AList.lookup (op =) vTs v)), Term Output)) missing_vars)
                @ acc_ps) true
            (case p of
                Prem t => union (op =) vs (term_vs t)
              | Sidecond t => union (op =) vs (term_vs t)
              | Negprem t => union (op =) vs (term_vs t)
              | _ => error "I do not know")
            (filter_out (equal p) ps)
          else NONE
        | SOME (p, NONE) => NONE
        | NONE => NONE)
  in
    case check_mode_prems [] false in_vs ps of
      NONE => NONE
    | SOME (acc_ps, vs, rnd) =>
      if forall (is_constructable thy vs) (in_ts @ out_ts) then
        SOME (ts, rev acc_ps, rnd)
      else
        if use_random then
          let
            val generators = map
              (fn v => (Generator (v, the (AList.lookup (op =) vTs v)), Term Output))
                (subtract (op =) vs (terms_vs out_ts))
          in
            SOME (ts, rev (generators @ acc_ps), true)
          end
        else
          NONE
  end

datatype result = Success of bool | Error of string

fun check_modes_pred' use_random options thy param_vs clauses modes (p, ms) =
  let
    fun split xs =
      let
        fun split' [] (ys, zs) = (rev ys, rev zs)
          | split' ((m, Error z) :: xs) (ys, zs) = split' xs (ys, z :: zs)
          | split' ((m, Success rnd) :: xs) (ys, zs) = split' xs ((m, rnd) :: ys, zs)
       in
         split' xs ([], [])
       end
    val rs = these (AList.lookup (op =) clauses p)
    fun check_mode m =
      let
        val res = map (check_mode_clause' use_random thy param_vs modes m) rs
      in
        case find_indices is_none res of
          [] => Success (exists (fn SOME (_, _, true) => true | _ => false) res)
        | is => (print_failed_mode options thy modes p m rs is; Error (error_of p m is))
      end
    val res = map (fn (m, _) => (m, check_mode m)) ms
    val (ms', errors) = split res
  in
    ((p, ms'), errors)
  end;

fun get_modes_pred' use_random thy param_vs clauses modes (p, ms) =
  let
    val rs = these (AList.lookup (op =) clauses p)
  in
    (p, map (fn (m, rnd) =>
      (m, map ((fn (ts, ps, rnd) => (ts, ps)) o the o check_mode_clause' use_random thy param_vs modes m) rs)) ms)
  end;

fun fixp f x =
  let val y = f x
  in if x = y then x else fixp f y end;

fun fixp_with_state f (x, state) =
  let
    val (y, state') = f (x, state)
  in
    if x = y then (y, state') else fixp_with_state f (y, state')
  end

fun infer_modes use_random options preds extra_modes param_vs clauses thy =
  let
    val all_modes = map (fn (s, T) => (s, map (rpair false) (all_modes_of_typ T))) preds
    fun needs_random s m = (m, member (op =) (#needs_random (the_pred_data thy s)) m)
    val extra_modes = map (fn (s, ms) => (s, map (needs_random s) ms)) extra_modes
    val (modes, errors) =
      fixp_with_state (fn (modes, errors) =>
        let
          val res = map
            (check_modes_pred' use_random options thy param_vs clauses (modes @ extra_modes)) modes
        in (map fst res, errors @ maps snd res) end)
          (all_modes, [])
    val thy' = fold (fn (s, ms) => if member (op =) (map fst preds) s then
      set_needs_random s (map fst (filter (fn (_, rnd) => rnd = true) ms)) else I) modes thy
  in
    ((map (get_modes_pred' use_random thy param_vs clauses (modes @ extra_modes)) modes, errors), thy')
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

fun mk_Eval_of additional_arguments ((x, T), NONE) names = (x, names)
  | mk_Eval_of additional_arguments ((x, T), SOME mode) names =
  let
    val Ts = binder_types T
    fun mk_split_lambda [] t = lambda (Free (Name.variant names "x", HOLogic.unitT)) t
      | mk_split_lambda [x] t = lambda x t
      | mk_split_lambda xs t =
      let
        fun mk_split_lambda' (x::y::[]) t = HOLogic.mk_split (lambda x (lambda y t))
          | mk_split_lambda' (x::xs) t = HOLogic.mk_split (lambda x (mk_split_lambda' xs t))
      in
        mk_split_lambda' xs t
      end;
    fun mk_arg (i, T) =
      let
        val vname = Name.variant names ("x" ^ string_of_int i)
        val default = Free (vname, T)
      in 
        case AList.lookup (op =) mode i of
          NONE => (([], [default]), [default])
        | SOME NONE => (([default], []), [default])
        | SOME (SOME pis) =>
          case HOLogic.strip_tupleT T of
            [] => error "pair mode but unit tuple" (*(([default], []), [default])*)
          | [_] => error "pair mode but not a tuple" (*(([default], []), [default])*)
          | Ts =>
            let
              val vnames = Name.variant_list names
                (map (fn j => "x" ^ string_of_int i ^ "p" ^ string_of_int j)
                  (1 upto length Ts))
              val args = map2 (curry Free) vnames Ts
              fun split_args (i, arg) (ins, outs) =
                if member (op =) pis i then
                  (arg::ins, outs)
                else
                  (ins, arg::outs)
              val (inargs, outargs) = fold_rev split_args ((1 upto length Ts) ~~ args) ([], [])
              fun tuple args = if null args then [] else [HOLogic.mk_tuple args]
            in ((tuple inargs, tuple outargs), args) end
      end
    val (inoutargs, args) = split_list (map mk_arg (1 upto (length Ts) ~~ Ts))
    val (inargs, outargs) = pairself flat (split_list inoutargs)
    val r = PredicateCompFuns.mk_Eval 
      (list_comb (x, inargs @ additional_arguments), HOLogic.mk_tuple outargs)
    val t = fold_rev mk_split_lambda args r
  in
    (t, names)
  end;

structure Comp_Mod =
struct

datatype comp_modifiers = Comp_Modifiers of
{
  compilation : compilation,
  function_name_prefix : string,
  compfuns : compilation_funs,
  additional_arguments : string list -> term list,
  wrap_compilation : compilation_funs -> string -> typ -> mode -> term list -> term -> term,
  transform_additional_arguments : indprem -> term list -> term list
}

fun dest_comp_modifiers (Comp_Modifiers c) = c

val compilation = #compilation o dest_comp_modifiers
val function_name_prefix = #function_name_prefix o dest_comp_modifiers
val compfuns = #compfuns o dest_comp_modifiers
val funT_of = funT_of o compfuns
val additional_arguments = #additional_arguments o dest_comp_modifiers
val wrap_compilation = #wrap_compilation o dest_comp_modifiers
val transform_additional_arguments = #transform_additional_arguments o dest_comp_modifiers

end;

(* TODO: uses param_vs -- change necessary for compilation with new modes *)
fun compile_arg compilation_modifiers compfuns additional_arguments thy param_vs iss arg = 
  let
    fun map_params (t as Free (f, T)) =
      if member (op =) param_vs f then
        case (AList.lookup (op =) (param_vs ~~ iss) f) of
          SOME is =>
            let
              val _ = error "compile_arg: A parameter in a input position -- do we have a test case?"
              val T' = Comp_Mod.funT_of compilation_modifiers is T
            in t(*fst (mk_Eval_of additional_arguments ((Free (f, T'), T), is) [])*) end
        | NONE => t
      else t
      | map_params t = t
    in map_aterms map_params arg end

fun compile_match compilation_modifiers compfuns additional_arguments
  param_vs iss thy eqs eqs' out_ts success_t =
  let
    val eqs'' = maps mk_eq eqs @ eqs'
    val eqs'' =
      map (compile_arg compilation_modifiers compfuns additional_arguments thy param_vs iss) eqs''
    val names = fold Term.add_free_names (success_t :: eqs'' @ out_ts) [];
    val name = Name.variant names "x";
    val name' = Name.variant (name :: names) "y";
    val T = HOLogic.mk_tupleT (map fastype_of out_ts);
    val U = fastype_of success_t;
    val U' = dest_predT compfuns U;
    val v = Free (name, T);
    val v' = Free (name', T);
  in
    lambda v (fst (Datatype.make_case
      (ProofContext.init thy) Datatype_Case.Quiet [] v
      [(HOLogic.mk_tuple out_ts,
        if null eqs'' then success_t
        else Const (@{const_name HOL.If}, HOLogic.boolT --> U --> U --> U) $
          foldr1 HOLogic.mk_conj eqs'' $ success_t $
            mk_bot compfuns U'),
       (v', mk_bot compfuns U')]))
  end;

fun compile_expr compilation_modifiers compfuns thy (t, deriv) additional_arguments =
  let
    fun expr_of (t, deriv) =
      (case (t, deriv) of
        (t, Term Input) => SOME t
      | (t, Term Output) => NONE
      | (Const (name, T), Context mode) =>
        SOME (Const (function_name_of (Comp_Mod.compilation compilation_modifiers) thy name mode,
          Comp_Mod.funT_of compilation_modifiers mode T))
      | (Free (s, T), Context m) =>
        SOME (Free (s, Comp_Mod.funT_of compilation_modifiers m T))
      | (t, Context m) =>
        let
          val bs = map (pair "x") (binder_types (fastype_of t))
          val bounds = map Bound (rev (0 upto (length bs) - 1))
        in SOME (list_abs (bs, mk_if compfuns (list_comb (t, bounds)))) end
      | (Const ("Pair", _) $ t1 $ t2, Mode_Pair (d1, d2)) =>
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
    the (expr_of (t, deriv))
  end

fun compile_clause compilation_modifiers compfuns thy all_vs param_vs additional_arguments
  mode inp (ts, moded_ps) =
  let
    val iss = ho_arg_modes_of mode
    val compile_match = compile_match compilation_modifiers compfuns
      additional_arguments param_vs iss thy
    val (in_ts, out_ts) = split_mode mode ts;
    val (in_ts', (all_vs', eqs)) =
      fold_map (collect_non_invertible_subterms thy) in_ts (all_vs, []);
    fun compile_prems out_ts' vs names [] =
          let
            val (out_ts'', (names', eqs')) =
              fold_map (collect_non_invertible_subterms thy) out_ts' (names, []);
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
              fold_map (collect_non_invertible_subterms thy) out_ts (names, [])
            val (out_ts'', (names'', constr_vs')) = fold_map distinct_v
              out_ts' ((names', map (rpair []) vs))
            val mode = head_mode_of deriv
            val additional_arguments' =
              Comp_Mod.transform_additional_arguments compilation_modifiers p additional_arguments
            val (compiled_clause, rest) = case p of
               Prem t =>
                 let
                   val u =
                     compile_expr compilation_modifiers compfuns thy
                       (t, deriv) additional_arguments'
                   val (_, out_ts''') = split_mode mode (snd (strip_comb t))
                   val rest = compile_prems out_ts''' vs' names'' ps
                 in
                   (u, rest)
                 end
             | Negprem t =>
                 let
                   val u = mk_not compfuns
                     (compile_expr compilation_modifiers compfuns thy
                       (t, deriv) additional_arguments')
                   val (_, out_ts''') = split_mode mode (snd (strip_comb t))
                   val rest = compile_prems out_ts''' vs' names'' ps
                 in
                   (u, rest)
                 end
             | Sidecond t =>
                 let
                   val t = compile_arg compilation_modifiers compfuns additional_arguments
                     thy param_vs iss t
                   val rest = compile_prems [] vs' names'' ps;
                 in
                   (mk_if compfuns t, rest)
                 end
             | Generator (v, T) =>
                 let
                   val u = mk_random T
                   val rest = compile_prems [Free (v, T)]  vs' names'' ps;
                 in
                   (u, rest)
                 end
          in
            compile_match constr_vs' eqs out_ts''
              (mk_bind compfuns (compiled_clause, rest))
          end
    val prem_t = compile_prems in_ts' param_vs all_vs' moded_ps;
  in
    mk_bind compfuns (mk_single compfuns inp, prem_t)
  end

fun compile_pred compilation_modifiers thy all_vs param_vs s T mode moded_cls =
  let
    (* TODO: val additional_arguments = Comp_Mod.additional_arguments compilation_modifiers
      (all_vs @ param_vs)
    *)
    val compfuns = Comp_Mod.compfuns compilation_modifiers
    fun is_param_type (T as Type ("fun",[_ , T'])) =
      is_some (try (dest_predT compfuns) T) orelse is_param_type T'
      | is_param_type T = is_some (try (dest_predT compfuns) T)
    val additional_arguments = []
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
    val cl_ts =
      map (compile_clause compilation_modifiers compfuns
        thy all_vs param_vs additional_arguments mode (HOLogic.mk_tuple in_ts')) moded_cls;
    val compilation = Comp_Mod.wrap_compilation compilation_modifiers compfuns
      s T mode additional_arguments
      (if null cl_ts then
        mk_bot compfuns (HOLogic.mk_tupleT outTs)
      else foldr1 (mk_sup compfuns) cl_ts)
    val fun_const =
      Const (function_name_of (Comp_Mod.compilation compilation_modifiers) thy s mode, funT)
  in
    HOLogic.mk_Trueprop
      (HOLogic.mk_eq (list_comb (fun_const, in_ts @ additional_arguments), compilation))
  end;

(* special setup for simpset *)                  
val HOL_basic_ss' = HOL_basic_ss addsimps (@{thms "HOL.simp_thms"} @ [@{thm Pair_eq}])
  setSolver (mk_solver "all_tac_solver" (fn _ => fn _ => all_tac))
  setSolver (mk_solver "True_solver" (fn _ => rtac @{thm TrueI}))

(* Definition of executable functions and their intro and elim rules *)

fun print_arities arities = tracing ("Arities:\n" ^
  cat_lines (map (fn (s, (ks, k)) => s ^ ": " ^
    space_implode " -> " (map
      (fn NONE => "X" | SOME k' => string_of_int k')
        (ks @ [SOME k]))) arities));

fun split_lambda (x as Free _) t = lambda x t
  | split_lambda (Const ("Pair", _) $ t1 $ t2) t =
    HOLogic.mk_split (split_lambda t1 (split_lambda t2 t))
  | split_lambda (Const ("Product_Type.Unity", _)) t = Abs ("x", HOLogic.unitT, t)
  | split_lambda t _ = raise (TERM ("split_lambda", [t]))

fun strip_split_abs (Const ("split", _) $ t) = strip_split_abs t
  | strip_split_abs (Abs (_, _, t)) = strip_split_abs t
  | strip_split_abs t = t

fun mk_args is_eval (Pair (m1, m2), Type ("*", [T1, T2])) names =
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

fun create_intro_elim_rule mode defthm mode_id funT pred thy =
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
    val introthm = Goal.prove (ProofContext.init thy)
      (argnames @ hoarg_names' @ ["y"]) [] introtrm (fn _ => unfolddef_tac)
    val P = HOLogic.mk_Trueprop (Free ("P", HOLogic.boolT));
    val elimtrm = Logic.list_implies ([funpropE, Logic.mk_implies (predpropE, P)], P)
    val elimthm = Goal.prove (ProofContext.init thy)
      (argnames @ ["y", "P"]) [] elimtrm (fn _ => unfolddef_tac)
  in
    (introthm, elimthm)
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
          PureThy.add_defs false [((Binding.name (mode_cbasename ^ "_def"), def), [])]
        val (intro, elim) =
          create_intro_elim_rule mode definition mode_cname funT (Const (name, T)) thy'
        in thy'
          |> set_function_name Pred name mode mode_cname
          |> add_predfun_data name mode (definition, intro, elim)
          |> PureThy.store_thm (Binding.name (mode_cbasename ^ "I"), intro) |> snd
          |> PureThy.store_thm (Binding.name (mode_cbasename ^ "E"), elim)  |> snd
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
        Const (name, _) => name mem_string constr_consts
        | _ => false) end))
  else false

(* MAJOR FIXME:  prove_params should be simple
 - different form of introrule for parameters ? *)

fun prove_param options thy t deriv =
  let
    val  (f, args) = strip_comb (Envir.eta_contract t)
    val mode = head_mode_of deriv
    val param_derivations = param_derivations_of deriv
    val ho_args = ho_args_of mode args
    val f_tac = case f of
      Const (name, T) => simp_tac (HOL_basic_ss addsimps 
         ([@{thm eval_pred}, (predfun_definition_of thy name mode),
         @{thm "split_eta"}, @{thm "split_beta"}, @{thm "fst_conv"},
         @{thm "snd_conv"}, @{thm pair_collapse}, @{thm "Product_Type.split_conv"}])) 1
    | Free _ => TRY (rtac @{thm refl} 1)
    | Abs _ => error "prove_param: No valid parameter term"
  in
    REPEAT_DETERM (rtac @{thm ext} 1)
    THEN print_tac' options "prove_param"
    THEN f_tac
    THEN print_tac' options "after simplification in prove_args"
    THEN (REPEAT_DETERM (atac 1))
    THEN (EVERY (map2 (prove_param options thy) ho_args param_derivations))
  end

fun prove_expr options thy (premposition : int) (t, deriv) =
  case strip_comb t of
    (Const (name, T), args) =>
      let
        val mode = head_mode_of deriv
        val introrule = predfun_intro_of thy name mode
        val param_derivations = param_derivations_of deriv
        val ho_args = ho_args_of mode args
      in
        print_tac' options "before intro rule:"
        (* for the right assumption in first position *)
        THEN rotate_tac premposition 1
        THEN debug_tac (Display.string_of_thm (ProofContext.init thy) introrule)
        THEN rtac introrule 1
        THEN print_tac' options "after intro rule"
        (* work with parameter arguments *)
        THEN atac 1
        THEN print_tac' options "parameter goal"
        THEN (EVERY (map2 (prove_param options thy) ho_args param_derivations))
        THEN (REPEAT_DETERM (atac 1))
      end
  | _ =>
    asm_full_simp_tac
      (HOL_basic_ss' addsimps [@{thm "split_eta"}, @{thm "split_beta"}, @{thm "fst_conv"},
         @{thm "snd_conv"}, @{thm pair_collapse}]) 1
    THEN (atac 1)
    THEN print_tac' options "after prove parameter call"


fun SOLVED tac st = FILTER (fn st' => nprems_of st' = nprems_of st - 1) tac st;

fun SOLVEDALL tac st = FILTER (fn st' => nprems_of st' = 0) tac st

fun check_format thy st =
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

fun prove_match options thy (out_ts : term list) =
  let
    fun get_case_rewrite t =
      if (is_constructor thy t) then let
        val case_rewrites = (#case_rewrites (Datatype.the_info thy
          ((fst o dest_Type o fastype_of) t)))
        in case_rewrites @ maps get_case_rewrite (snd (strip_comb t)) end
      else []
    val simprules = @{thm "unit.cases"} :: @{thm "prod.cases"} :: maps get_case_rewrite out_ts
  (* replace TRY by determining if it necessary - are there equations when calling compile match? *)
  in
     (* make this simpset better! *)
    asm_full_simp_tac (HOL_basic_ss' addsimps simprules) 1
    THEN print_tac' options "after prove_match:"
    THEN (DETERM (TRY (EqSubst.eqsubst_tac (ProofContext.init thy) [0] [@{thm "HOL.if_P"}] 1
           THEN (REPEAT_DETERM (rtac @{thm conjI} 1 THEN (SOLVED (asm_simp_tac HOL_basic_ss' 1))))
           THEN print_tac' options "if condition to be solved:"
           THEN (SOLVED (asm_simp_tac HOL_basic_ss' 1 THEN print_tac' options "after if simp; in SOLVED:"))
           THEN check_format thy
           THEN print_tac' options "after if simplification - a TRY block")))
    THEN print_tac' options "after if simplification"
  end;

(* corresponds to compile_fun -- maybe call that also compile_sidecond? *)

fun prove_sidecond thy modes t =
  let
    fun preds_of t nameTs = case strip_comb t of 
      (f as Const (name, T), args) =>
        if AList.defined (op =) modes name then (name, T) :: nameTs
          else fold preds_of args nameTs
      | _ => nameTs
    val preds = preds_of t []
    val defs = map
      (fn (pred, T) => predfun_definition_of thy pred
        (all_input_of T))
        preds
  in 
    (* remove not_False_eq_True when simpset in prove_match is better *)
    simp_tac (HOL_basic_ss addsimps
      (@{thms "HOL.simp_thms"} @ (@{thm not_False_eq_True} :: @{thm eval_pred} :: defs))) 1 
    (* need better control here! *)
  end

fun prove_clause options thy nargs modes mode (_, clauses) (ts, moded_ps) =
  let
    val (in_ts, clause_out_ts) = split_mode mode ts;
    fun prove_prems out_ts [] =
      (prove_match options thy out_ts)
      THEN print_tac' options "before simplifying assumptions"
      THEN asm_full_simp_tac HOL_basic_ss' 1
      THEN print_tac' options "before single intro rule"
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
              print_tac' options "before clause:"
              (*THEN asm_simp_tac HOL_basic_ss 1*)
              THEN print_tac' options "before prove_expr:"
              THEN prove_expr options thy premposition (t, deriv)
              THEN print_tac' options "after prove_expr:"
              THEN rec_tac
            end
          | Negprem t =>
            let
              val (t, args) = strip_comb t
              val (_, out_ts''') = split_mode mode args
              val rec_tac = prove_prems out_ts''' ps
              val name = (case strip_comb t of (Const (c, _), _) => SOME c | _ => NONE)
              val param_derivations = param_derivations_of deriv
              val params = ho_args_of mode args
            in
              print_tac' options "before prove_neg_expr:"
              THEN full_simp_tac (HOL_basic_ss addsimps
                [@{thm split_eta}, @{thm split_beta}, @{thm fst_conv},
                 @{thm snd_conv}, @{thm pair_collapse}, @{thm Product_Type.split_conv}]) 1
              THEN (if (is_some name) then
                  print_tac' options ("before unfolding definition " ^
                    (Display.string_of_thm_global thy
                      (predfun_definition_of thy (the name) mode)))
                  
                  THEN simp_tac (HOL_basic_ss addsimps
                    [predfun_definition_of thy (the name) mode]) 1
                  THEN rtac @{thm not_predI} 1
                  THEN print_tac' options "after applying rule not_predI"
                  THEN full_simp_tac (HOL_basic_ss addsimps [@{thm not_False_eq_True},
                    @{thm split_eta}, @{thm split_beta}, @{thm fst_conv},
                    @{thm snd_conv}, @{thm pair_collapse}, @{thm Product_Type.split_conv}]) 1
                  THEN (REPEAT_DETERM (atac 1))
                  THEN (EVERY (map2 (prove_param options thy) params param_derivations))
                  THEN (REPEAT_DETERM (atac 1))
                else
                  rtac @{thm not_predI'} 1)
                  THEN simp_tac (HOL_basic_ss addsimps [@{thm not_False_eq_True}]) 1
              THEN rec_tac
            end
          | Sidecond t =>
           rtac @{thm if_predI} 1
           THEN print_tac' options "before sidecond:"
           THEN prove_sidecond thy modes t
           THEN print_tac' options "after sidecond:"
           THEN prove_prems [] ps)
      in (prove_match options thy out_ts)
          THEN rest_tac
      end;
    val prems_tac = prove_prems in_ts moded_ps
  in
    print_tac' options "Proving clause..."
    THEN rtac @{thm bindI} 1
    THEN rtac @{thm singleI} 1
    THEN prems_tac
  end;

fun select_sup 1 1 = []
  | select_sup _ 1 = [rtac @{thm supI1}]
  | select_sup n i = (rtac @{thm supI2})::(select_sup (n - 1) (i - 1));

fun prove_one_direction options thy clauses preds modes pred mode moded_clauses =
  let
    val T = the (AList.lookup (op =) preds pred)
    val nargs = length (binder_types T)
    val pred_case_rule = the_elim_of thy pred
  in
    REPEAT_DETERM (CHANGED (rewtac @{thm "split_paired_all"}))
    THEN print_tac' options "before applying elim rule"
    THEN etac (predfun_elim_of thy pred mode) 1
    THEN etac pred_case_rule 1
    THEN (EVERY (map
           (fn i => EVERY' (select_sup (length moded_clauses) i) i) 
             (1 upto (length moded_clauses))))
    THEN (EVERY (map2 (prove_clause options thy nargs modes mode) clauses moded_clauses))
    THEN print_tac' options "proved one direction"
  end;

(** Proof in the other direction **)

fun prove_match2 thy out_ts = let
  fun split_term_tac (Free _) = all_tac
    | split_term_tac t =
      if (is_constructor thy t) then let
        val info = Datatype.the_info thy ((fst o dest_Type o fastype_of) t)
        val num_of_constrs = length (#case_rewrites info)
        (* special treatment of pairs -- because of fishing *)
        val split_rules = case (fst o dest_Type o fastype_of) t of
          "*" => [@{thm prod.split_asm}] 
          | _ => PureThy.get_thms thy (((fst o dest_Type o fastype_of) t) ^ ".split_asm")
        val (_, ts) = strip_comb t
      in
        (print_tac ("Term " ^ (Syntax.string_of_term_global thy t) ^ 
          "splitting with rules \n" ^
        commas (map (Display.string_of_thm_global thy) split_rules)))
        THEN TRY ((Splitter.split_asm_tac split_rules 1)
        THEN (print_tac "after splitting with split_asm rules")
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

fun prove_param2 thy t deriv =
  let
    val (f, args) = strip_comb (Envir.eta_contract t)
    val mode = head_mode_of deriv
    val param_derivations = param_derivations_of deriv
    val ho_args = ho_args_of mode args
    val f_tac = case f of
        Const (name, T) => full_simp_tac (HOL_basic_ss addsimps 
           (@{thm eval_pred}::(predfun_definition_of thy name mode)
           :: @{thm "Product_Type.split_conv"}::[])) 1
      | Free _ => all_tac
      | _ => error "prove_param2: illegal parameter term"
  in
    print_tac "before simplification in prove_args:"
    THEN f_tac
    THEN print_tac "after simplification in prove_args"
    THEN EVERY (map2 (prove_param2 thy) ho_args param_derivations)
  end

fun prove_expr2 thy (t, deriv) = 
  (case strip_comb t of
      (Const (name, T), args) =>
        let
          val mode = head_mode_of deriv
          val param_derivations = param_derivations_of deriv
          val ho_args = ho_args_of mode args
        in
          etac @{thm bindE} 1
          THEN (REPEAT_DETERM (CHANGED (rewtac @{thm "split_paired_all"})))
          THEN print_tac "prove_expr2-before"
          THEN (debug_tac (Syntax.string_of_term_global thy
            (prop_of (predfun_elim_of thy name mode))))
          THEN (etac (predfun_elim_of thy name mode) 1)
          THEN print_tac "prove_expr2"
          THEN (EVERY (map2 (prove_param2 thy) ho_args param_derivations))
          THEN print_tac "finished prove_expr2"
        end
      | _ => etac @{thm bindE} 1)

(* FIXME: what is this for? *)
(* replace defined by has_mode thy pred *)
(* TODO: rewrite function *)
fun prove_sidecond2 thy modes t = let
  fun preds_of t nameTs = case strip_comb t of 
    (f as Const (name, T), args) =>
      if AList.defined (op =) modes name then (name, T) :: nameTs
        else fold preds_of args nameTs
    | _ => nameTs
  val preds = preds_of t []
  val defs = map
    (fn (pred, T) => predfun_definition_of thy pred 
      (all_input_of T))
      preds
  in
   (* only simplify the one assumption *)
   full_simp_tac (HOL_basic_ss' addsimps @{thm eval_pred} :: defs) 1 
   (* need better control here! *)
   THEN print_tac "after sidecond2 simplification"
   end
  
fun prove_clause2 thy modes pred mode (ts, ps) i =
  let
    val pred_intro_rule = nth (intros_of thy pred) (i - 1)
    val (in_ts, clause_out_ts) = split_mode mode ts;
    fun prove_prems2 out_ts [] =
      print_tac "before prove_match2 - last call:"
      THEN prove_match2 thy out_ts
      THEN print_tac "after prove_match2 - last call:"
      THEN (etac @{thm singleE} 1)
      THEN (REPEAT_DETERM (etac @{thm Pair_inject} 1))
      THEN (asm_full_simp_tac HOL_basic_ss' 1)
      THEN (REPEAT_DETERM (etac @{thm Pair_inject} 1))
      THEN (asm_full_simp_tac HOL_basic_ss' 1)
      THEN SOLVED (print_tac "state before applying intro rule:"
      THEN (rtac pred_intro_rule 1)
      (* How to handle equality correctly? *)
      THEN (print_tac "state before assumption matching")
      THEN (REPEAT (atac 1 ORELSE 
         (CHANGED (asm_full_simp_tac (HOL_basic_ss' addsimps
           [@{thm split_eta}, @{thm "split_beta"}, @{thm "fst_conv"},
             @{thm "snd_conv"}, @{thm pair_collapse}]) 1)
          THEN print_tac "state after simp_tac:"))))
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
            (prove_expr2 thy (t, deriv)) THEN rec_tac
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
            print_tac "before neg prem 2"
            THEN etac @{thm bindE} 1
            THEN (if is_some name then
                full_simp_tac (HOL_basic_ss addsimps
                  [predfun_definition_of thy (the name) mode]) 1
                THEN etac @{thm not_predE} 1
                THEN simp_tac (HOL_basic_ss addsimps [@{thm not_False_eq_True}]) 1
                THEN (EVERY (map2 (prove_param2 thy) ho_args param_derivations))
              else
                etac @{thm not_predE'} 1)
            THEN rec_tac
          end 
        | Sidecond t =>
          etac @{thm bindE} 1
          THEN etac @{thm if_predE} 1
          THEN prove_sidecond2 thy modes t 
          THEN prove_prems2 [] ps)
      in print_tac "before prove_match2:"
         THEN prove_match2 thy out_ts
         THEN print_tac "after prove_match2:"
         THEN rest_tac
      end;
    val prems_tac = prove_prems2 in_ts ps 
  in
    print_tac "starting prove_clause2"
    THEN etac @{thm bindE} 1
    THEN (etac @{thm singleE'} 1)
    THEN (TRY (etac @{thm Pair_inject} 1))
    THEN print_tac "after singleE':"
    THEN prems_tac
  end;
 
fun prove_other_direction options thy modes pred mode moded_clauses =
  let
    fun prove_clause clause i =
      (if i < length moded_clauses then etac @{thm supE} 1 else all_tac)
      THEN (prove_clause2 thy modes pred mode clause i)
  in
    (DETERM (TRY (rtac @{thm unit.induct} 1)))
     THEN (REPEAT_DETERM (CHANGED (rewtac @{thm split_paired_all})))
     THEN (rtac (predfun_intro_of thy pred mode) 1)
     THEN (REPEAT_DETERM (rtac @{thm refl} 2))
     THEN (if null moded_clauses then
         etac @{thm botE} 1
       else EVERY (map2 prove_clause moded_clauses (1 upto (length moded_clauses))))
  end;

(** proof procedure **)

fun prove_pred options thy clauses preds modes pred mode (moded_clauses, compiled_term) =
  let
    val ctxt = ProofContext.init thy
    val clauses = case AList.lookup (op =) clauses pred of SOME rs => rs | NONE => []
  in
    Goal.prove ctxt (Term.add_free_names compiled_term []) [] compiled_term
      (if not (skip_proof options) then
        (fn _ =>
        rtac @{thm pred_iffI} 1
        THEN print_tac' options "after pred_iffI"
        THEN prove_one_direction options thy clauses preds modes pred mode moded_clauses
        THEN print_tac' options "proved one direction"
        THEN prove_other_direction options thy modes pred mode moded_clauses
        THEN print_tac' options "proved other direction")
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
    
fun compile_preds comp_modifiers thy all_vs param_vs preds moded_clauses =
  map_preds_modes (fn pred => compile_pred comp_modifiers thy all_vs param_vs pred
      (the (AList.lookup (op =) preds pred))) moded_clauses

fun prove options thy clauses preds modes moded_clauses compiled_terms =
  map_preds_modes (prove_pred options thy clauses preds modes)
    (join_preds_modes moded_clauses compiled_terms)

fun prove_by_skip options thy _ _ _ _ compiled_terms =
  map_preds_modes (fn pred => fn mode => fn t => Drule.standard (Skip_Proof.make_thm thy t))
    compiled_terms

(* preparation of introduction rules into special datastructures *)

fun dest_prem thy params t =
  (case strip_comb t of
    (v as Free _, ts) => if member (op =) params v then Prem t else Sidecond t
  | (c as Const (@{const_name Not}, _), [t]) => (case dest_prem thy params t of
      Prem t => Negprem t
    | Negprem _ => error ("Double negation not allowed in premise: " ^
        Syntax.string_of_term_global thy (c $ t)) 
    | Sidecond t => Sidecond (c $ t))
  | (c as Const (s, _), ts) =>
    if is_registered thy s then Prem t else Sidecond t
  | _ => Sidecond t)

fun prepare_intrs options compilation thy prednames intros =
  let
    val intrs = map prop_of intros
    val preds = map (fn c => Const (c, Sign.the_const_type thy c)) prednames
    val (preds, intrs) = unify_consts thy preds intrs
    val ([preds, intrs], _) = fold_burrow (Variable.import_terms false) [preds, intrs]
      (ProofContext.init thy)
    val preds = map dest_Const preds
    val extra_modes =
      all_modes_of compilation thy |> filter_out (fn (name, _) => member (op =) prednames name)
    val all_vs = terms_vs intrs
    val params =
      case intrs of
        [] =>
          let
            val T = snd (hd preds)
            val paramTs =
              ho_argsT_of (hd (all_modes_of_typ T)) (binder_types T)
            val param_names = Name.variant_list [] (map (fn i => "p" ^ string_of_int i)
              (1 upto length paramTs))
          in
            map2 (curry Free) param_names paramTs
          end
      | (intr :: _) => maps extract_params
          (snd (strip_comb (HOLogic.dest_Trueprop (Logic.strip_imp_concl intr))))
    val param_vs = map (fst o dest_Free) params
    fun add_clause intr clauses =
      let
        val (Const (name, T), ts) = strip_comb (HOLogic.dest_Trueprop (Logic.strip_imp_concl intr))
        val prems = map (dest_prem thy params o HOLogic.dest_Trueprop) (Logic.strip_imp_prems intr)
      in
        AList.update op = (name, these (AList.lookup op = clauses name) @
          [(ts, prems)]) clauses
      end;
    val clauses = fold add_clause intrs []
  in
    (preds, all_vs, param_vs, extra_modes, clauses)
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
          (Drule.standard o (Skip_Proof.make_thm thy))
          (mk_casesrule (ProofContext.init thy) nparams intros)
      in
        if not (Thm.equiv_thm (elim, elim')) then
          error "Introduction and elimination rules do not match!"
        else true
      end
  in forall check prednames end
*)

(* create code equation *)

fun add_code_equations thy preds result_thmss =
  let
    fun add_code_equation (predname, T) (pred, result_thms) =
      let
        val full_mode = fold_rev (curry Fun) (map (K Input) (binder_types T)) Bool
      in
        if member (op =) (modes_of Pred thy predname) full_mode then
          let
            val Ts = binder_types T
            val arg_names = Name.variant_list []
              (map (fn i => "x" ^ string_of_int i) (1 upto length Ts))
            val args = map2 (curry Free) arg_names Ts
            val predfun = Const (function_name_of Pred thy predname full_mode,
              Ts ---> PredicateCompFuns.mk_predT @{typ unit})
            val rhs = @{term Predicate.holds} $ (list_comb (predfun, args))
            val eq_term = HOLogic.mk_Trueprop
              (HOLogic.mk_eq (list_comb (Const (predname, T), args), rhs))
            val def = predfun_definition_of thy predname full_mode
            val tac = fn _ => Simplifier.simp_tac
              (HOL_basic_ss addsimps [def, @{thm holds_eq}, @{thm eval_pred}]) 1
            val eq = Goal.prove (ProofContext.init thy) arg_names [] eq_term tac
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
  define_functions : options -> (string * typ) list -> string * mode list -> theory -> theory,
  infer_modes : options -> (string * typ) list -> (string * mode list) list
    -> string list -> (string * (term list * indprem list) list) list
    -> theory -> ((moded_clause list pred_mode_table * string list) * theory),
  prove : options -> theory -> (string * (term list * indprem list) list) list
    -> (string * typ) list -> (string * mode list) list
    -> moded_clause list pred_mode_table -> term pred_mode_table -> thm pred_mode_table,
  add_code_equations : theory -> (string * typ) list
    -> (string * thm list) list -> (string * thm list) list,
  comp_modifiers : Comp_Mod.comp_modifiers,
  qname : bstring
  }

fun add_equations_of steps options prednames thy =
  let
    fun dest_steps (Steps s) = s
    val _ = print_step options
      ("Starting predicate compiler for predicates " ^ commas prednames ^ "...")
      (*val _ = check_intros_elim_match thy prednames*)
      (*val _ = map (check_format_of_intro_rule thy) (maps (intros_of thy) prednames)*)
    val compilation = Comp_Mod.compilation (#comp_modifiers (dest_steps steps))
    val (preds, all_vs, param_vs, extra_modes, clauses) =
      prepare_intrs options compilation thy prednames (maps (intros_of thy) prednames)
    val _ = print_step options "Infering modes..."
    val ((moded_clauses, errors), thy') =
      #infer_modes (dest_steps steps) options preds extra_modes param_vs clauses thy
    val modes = map (fn (p, mps) => (p, map fst mps)) moded_clauses
    val _ = check_expected_modes preds options modes
    val _ = check_proposed_modes preds options modes extra_modes errors
    val _ = print_modes options thy' modes
    val _ = print_step options "Defining executable functions..."
    val thy'' = fold (#define_functions (dest_steps steps) options preds) modes thy'
      |> Theory.checkpoint
    val _ = print_step options "Compiling equations..."
    val compiled_terms =
      compile_preds (#comp_modifiers (dest_steps steps)) thy'' all_vs param_vs preds moded_clauses
    val _ = print_compiled_terms options thy'' compiled_terms
    val _ = print_step options "Proving equations..."
    val result_thms = #prove (dest_steps steps) options thy'' clauses preds (extra_modes @ modes)
      moded_clauses compiled_terms
    val result_thms' = #add_code_equations (dest_steps steps) thy'' preds
      (maps_modes result_thms)
    val qname = #qname (dest_steps steps)
    val attrib = fn thy => Attrib.attribute_i thy (Attrib.internal (K (Thm.declaration_attribute
      (fn thm => Context.mapping (Code.add_eqn thm) I))))
    val thy''' = fold (fn (name, result_thms) => fn thy => snd (PureThy.add_thmss
      [((Binding.qualify true (Long_Name.base_name name) (Binding.name qname), result_thms),
        [attrib thy ])] thy))
      result_thms' thy'' |> Theory.checkpoint
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
    val thy' = thy
      |> PredData.map (fold (extend (fetch_pred_data thy) (depending_preds_of thy)) names)
      |> Theory.checkpoint;
    fun strong_conn_of gr keys =
      Graph.strong_conn (Graph.subgraph (member (op =) (Graph.all_succs gr keys)) gr)
    val scc = strong_conn_of (PredData.get thy') names
    
    val thy'' = fold_rev
      (fn preds => fn thy =>
        if not (forall (defined thy) preds) then
          add_equations_of steps options preds thy
        else thy)
      scc thy' |> Theory.checkpoint
  in thy'' end
(*
val depth_limited_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = Depth_Limited,
  function_name_of = function_name_of Depth_Limited,
  set_function_name = set_function_name Depth_Limited,
  funT_of = depth_limited_funT_of : (compilation_funs -> mode -> typ -> typ),
  function_name_prefix = "depth_limited_",
  additional_arguments = fn names =>
    let
      val [depth_name, polarity_name] = Name.variant_list names ["depth", "polarity"]
    in [Free (polarity_name, @{typ "bool"}), Free (depth_name, @{typ "code_numeral"})] end,
  wrap_compilation =
    fn compfuns => fn s => fn T => fn mode => fn additional_arguments => fn compilation =>
    let
      val [polarity, depth] = additional_arguments
      val (_, Ts2) = chop (length (fst mode)) (binder_types T)
      val (_, Us2) = split_smodeT (snd mode) Ts2
      val T' = mk_predT compfuns (HOLogic.mk_tupleT Us2)
      val if_const = Const (@{const_name "If"}, @{typ bool} --> T' --> T' --> T')
      val full_mode = null Us2
    in
      if_const $ HOLogic.mk_eq (depth, @{term "0 :: code_numeral"})
        $ (if_const $ polarity $ mk_bot compfuns (dest_predT compfuns T')
          $ (if full_mode then mk_single compfuns HOLogic.unit else
            Const (@{const_name undefined}, T')))
        $ compilation
    end,
  transform_additional_arguments =
    fn prem => fn additional_arguments =>
    let
      val [polarity, depth] = additional_arguments
      val polarity' = (case prem of Prem _ => I | Negprem _ => HOLogic.mk_not | _ => I) polarity
      val depth' =
        Const ("HOL.minus_class.minus", @{typ "code_numeral => code_numeral => code_numeral"})
          $ depth $ Const ("HOL.one_class.one", @{typ "Code_Numeral.code_numeral"})
    in [polarity', depth'] end
  }

val random_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = Random,
  function_name_of = function_name_of Random,
  set_function_name = set_function_name Random,
  function_name_prefix = "random_",
  funT_of = K random_function_funT_of : (compilation_funs -> mode -> typ -> typ),
  additional_arguments = fn names => [Free (Name.variant names "size", @{typ code_numeral})],
  wrap_compilation = K (K (K (K (K I))))
    : (compilation_funs -> string -> typ -> mode -> term list -> term -> term),
  transform_additional_arguments = K I : (indprem -> term list -> term list)
  }
*)
(* different instantiantions of the predicate compiler *)

val predicate_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = Pred,
  function_name_prefix = "",
  compfuns = PredicateCompFuns.compfuns,
  additional_arguments = K [],
  wrap_compilation = K (K (K (K (K I))))
   : (compilation_funs -> string -> typ -> mode -> term list -> term -> term),
  transform_additional_arguments = K I : (indprem -> term list -> term list)
  }

val add_equations = gen_add_equations
  (Steps {infer_modes = infer_modes false,
  define_functions = create_definitions,
  prove = prove,
  add_code_equations = add_code_equations,
  comp_modifiers = predicate_comp_modifiers,
  qname = "equation"})

val annotated_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = Annotated,
  function_name_prefix = "annotated_",
  compfuns = PredicateCompFuns.compfuns,
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
  additional_arguments = K [],
  wrap_compilation = K (K (K (K (K I))))
   : (compilation_funs -> string -> typ -> mode -> term list -> term -> term),
  transform_additional_arguments = K I : (indprem -> term list -> term list)
  }

val random_dseq_comp_modifiers = Comp_Mod.Comp_Modifiers
  {
  compilation = Random_DSeq,
  function_name_prefix = "random_dseq_",
  compfuns = Random_Sequence_CompFuns.compfuns,
  additional_arguments = K [],
  wrap_compilation = K (K (K (K (K I))))
   : (compilation_funs -> string -> typ -> mode -> term list -> term -> term),
  transform_additional_arguments = K I : (indprem -> term list -> term list)
  }

(*
val add_depth_limited_equations = gen_add_equations
  (Steps {infer_modes = infer_modes,
  define_functions = define_functions depth_limited_comp_modifiers PredicateCompFuns.compfuns,
  compile_preds = compile_preds depth_limited_comp_modifiers PredicateCompFuns.compfuns,
  prove = prove_by_skip,
  add_code_equations = K (K I),
  defined = defined_functions Depth_Limited,
  qname = "depth_limited_equation"})
*)
val add_annotated_equations = gen_add_equations
  (Steps {infer_modes = infer_modes false,
  define_functions = define_functions annotated_comp_modifiers PredicateCompFuns.compfuns,
  prove = prove_by_skip,
  add_code_equations = K (K I),
  comp_modifiers = annotated_comp_modifiers,
  qname = "annotated_equation"})
(*
val add_quickcheck_equations = gen_add_equations
  (Steps {infer_modes = infer_modes_with_generator,
  define_functions = define_functions random_comp_modifiers RandomPredCompFuns.compfuns,
  compile_preds = compile_preds random_comp_modifiers RandomPredCompFuns.compfuns,
  prove = prove_by_skip,
  add_code_equations = K (K I),
  defined = defined_functions Random,
  qname = "random_equation"})
*)
val add_dseq_equations = gen_add_equations
  (Steps {infer_modes = infer_modes false,
  define_functions = define_functions dseq_comp_modifiers DSequence_CompFuns.compfuns,
  prove = prove_by_skip,
  add_code_equations = K (K I),
  comp_modifiers = dseq_comp_modifiers,
  qname = "dseq_equation"})

val add_random_dseq_equations = gen_add_equations
  (Steps {infer_modes = infer_modes true,
  define_functions = define_functions random_dseq_comp_modifiers Random_Sequence_CompFuns.compfuns,
  prove = prove_by_skip,
  add_code_equations = K (K I),
  comp_modifiers = random_dseq_comp_modifiers,
  qname = "random_dseq_equation"})


(** user interface **)

(* code_pred_intro attribute *)

fun attrib f = Thm.declaration_attribute (fn thm => Context.mapping (f thm) I);

val code_pred_intro_attrib = attrib add_intro;


(*FIXME
- Naming of auxiliary rules necessary?
*)

val setup = PredData.put (Graph.empty) #>
  Attrib.setup @{binding code_pred_intro} (Scan.succeed (attrib add_intro))
    "adding alternative introduction rules for code generation of inductive predicates"

(* TODO: make Theory_Data to Generic_Data & remove duplication of local theory and theory *)
fun generic_code_pred prep_const options raw_const lthy =
  let
    val thy = ProofContext.theory_of lthy
    val const = prep_const thy raw_const
    val lthy' = Local_Theory.theory (PredData.map
        (extend (fetch_pred_data thy) (depending_preds_of thy) const)) lthy
      |> Local_Theory.checkpoint
    val thy' = ProofContext.theory_of lthy'
    val preds = Graph.all_succs (PredData.get thy') [const] |> filter_out (has_elim thy')
    fun mk_cases const =
      let
        val T = Sign.the_const_type thy const
        val pred = Const (const, T)
        val intros = intros_of thy' const
      in mk_casesrule lthy' pred intros end  
    val cases_rules = map mk_cases preds
    val cases =
      map (fn case_rule => Rule_Cases.Case {fixes = [],
        assumes = [("", Logic.strip_imp_prems case_rule)],
        binds = [], cases = []}) cases_rules
    val case_env = map2 (fn p => fn c => (Long_Name.base_name p, SOME c)) preds cases
    val lthy'' = lthy'
      |> fold Variable.auto_fixes cases_rules 
      |> ProofContext.add_cases true case_env
    fun after_qed thms goal_ctxt =
      let
        val global_thms = ProofContext.export goal_ctxt
          (ProofContext.init (ProofContext.theory_of goal_ctxt)) (map the_single thms)
      in
        goal_ctxt |> Local_Theory.theory (fold set_elim global_thms #>
          ((case compilation options of
             Pred => add_equations
           | DSeq => add_dseq_equations
           | Random_DSeq => add_random_dseq_equations
           | compilation => error ("Compilation not supported")
           (*| Random => (fn opt => fn cs => add_equations opt cs #> add_quickcheck_equations opt cs)
           | Depth_Limited => add_depth_limited_equations
           | Annotated => add_annotated_equations*)
           ) options [const]))
      end
  in
    Proof.theorem_i NONE after_qed (map (single o (rpair [])) cases_rules) lthy''
  end;

val code_pred = generic_code_pred (K I);
val code_pred_cmd = generic_code_pred Code.read_const

(* transformation for code generation *)

val eval_ref = Unsynchronized.ref (NONE : (unit -> term Predicate.pred) option);
val random_eval_ref =
  Unsynchronized.ref (NONE : (unit -> int * int -> term Predicate.pred * (int * int)) option);
val dseq_eval_ref = Unsynchronized.ref (NONE : (unit -> term DSequence.dseq) option);
val random_dseq_eval_ref =
  Unsynchronized.ref (NONE : (unit -> int -> int -> int * int -> term DSequence.dseq * (int * int)) option);

(*FIXME turn this into an LCF-guarded preprocessor for comprehensions*)
fun analyze_compr thy compfuns param_user_modes (compilation, arguments) t_compr =
  let
    val all_modes_of = all_modes_of compilation
    val split = case t_compr of (Const (@{const_name Collect}, _) $ t) => t
      | _ => error ("Not a set comprehension: " ^ Syntax.string_of_term_global thy t_compr);
    val (body, Ts, fp) = HOLogic.strip_psplits split;
    val output_names = Name.variant_list (Term.add_free_names body [])
      (map (fn i => "x" ^ string_of_int i) (1 upto length Ts))
    val output_frees = map2 (curry Free) output_names Ts
    val body = subst_bounds (output_frees, body)
    val T_compr = HOLogic.mk_ptupleT fp (rev Ts)
    val output_tuple = HOLogic.mk_ptuple fp T_compr (rev output_frees)
    val (pred as Const (name, T), all_args) = strip_comb body
  in
    if defined_functions compilation thy name then
      let
        fun extract_mode (Const ("Pair", _) $ t1 $ t2) = Pair (extract_mode t1, extract_mode t2)
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
              | instance_of _ = false
          in forall instance_of (strip_fun_mode m1 ~~ strip_fun_mode m2) end
        val derivs = all_derivations_of thy (all_modes_of thy) [] body
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
                    ^ Syntax.string_of_term_global thy t_compr)
          | [d] => d
          | d :: _ :: _ => (warning ("Multiple modes possible for comprehension "
                    ^ Syntax.string_of_term_global thy t_compr); d);
        val (_, outargs) = split_mode (head_mode_of deriv) all_args
        val additional_arguments =
          case compilation of
            Pred => []
          | Random => [@{term "5 :: code_numeral"}]
          | Annotated => []
          | Depth_Limited => [@{term "True"}, HOLogic.mk_number @{typ "code_numeral"} (hd arguments)]
          | DSeq => []
          | Random_DSeq => []
        val comp_modifiers =
          case compilation of
            Pred => predicate_comp_modifiers
          (*| Random => random_comp_modifiers
          | Depth_Limited => depth_limited_comp_modifiers
          | Annotated => annotated_comp_modifiers*)
          | DSeq => dseq_comp_modifiers
          | Random_DSeq => random_dseq_comp_modifiers
        val t_pred = compile_expr comp_modifiers compfuns thy (body, deriv) additional_arguments;
        val T_pred = dest_predT compfuns (fastype_of t_pred)
        val arrange = split_lambda (HOLogic.mk_tuple outargs) output_tuple
      in
        if null outargs then t_pred else mk_map compfuns T_pred T_compr arrange t_pred
      end
    else
      error "Evaluation with values is not possible because compilation with code_pred was not invoked"
  end

fun eval thy param_user_modes (options as (compilation, arguments)) k t_compr =
  let
    val compfuns =
      case compilation of
        Random => RandomPredCompFuns.compfuns
      | DSeq => DSequence_CompFuns.compfuns
      | Random_DSeq => Random_Sequence_CompFuns.compfuns
      | _ => PredicateCompFuns.compfuns
    val t = analyze_compr thy compfuns param_user_modes options t_compr;
    val T = dest_predT compfuns (fastype_of t);
    val t' = mk_map compfuns T HOLogic.termT (HOLogic.term_of_const T) t;
    val ts =
      case compilation of
        Random =>
          fst (Predicate.yieldn k
          (Code_Eval.eval NONE ("Predicate_Compile_Core.random_eval_ref", random_eval_ref)
            (fn proc => fn g => fn s => g s |>> Predicate.map proc) thy t' []
            |> Random_Engine.run))
      | Random_DSeq =>
          let
            val [nrandom, size, depth] = arguments
          in
            fst (DSequence.yieldn k
              (Code_Eval.eval NONE ("Predicate_Compile_Core.random_dseq_eval_ref", random_dseq_eval_ref)
                (fn proc => fn g => fn nrandom => fn size => fn s => g nrandom size s |>> DSequence.map proc)
                  thy t' [] nrandom size
                |> Random_Engine.run)
              depth true)
          end
      | DSeq =>
          fst (DSequence.yieldn k
            (Code_Eval.eval NONE ("Predicate_Compile_Core.dseq_eval_ref", dseq_eval_ref)
              DSequence.map thy t' []) (the_single arguments) true)
      | _ =>
          fst (Predicate.yieldn k
            (Code_Eval.eval NONE ("Predicate_Compile_Core.eval_ref", eval_ref)
              Predicate.map thy t' []))
  in (T, ts) end;

fun values ctxt param_user_modes (raw_expected, comp_options) k t_compr =
  let
    val thy = ProofContext.theory_of ctxt
    val (T, ts) = eval thy param_user_modes comp_options k t_compr
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
    if k = ~1 orelse length ts < k then elems
      else Const (@{const_name Set.union}, setT --> setT --> setT) $ elems $ cont
  end;

fun values_cmd print_modes param_user_modes options k raw_t state =
  let
    val ctxt = Toplevel.context_of state
    val t = Syntax.read_term ctxt raw_t
    val t' = values ctxt param_user_modes options k t
    val ty' = Term.type_of t'
    val ctxt' = Variable.auto_fixes t' ctxt
    val p = PrintMode.with_modes print_modes (fn () =>
      Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' ty')]) ();
  in Pretty.writeln p end;

end;
