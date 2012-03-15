(*  Title:      HOL/Tools/Predicate_Compile/predicate_compile.ML
    Author:     Lukas Bulwahn, TU Muenchen

Entry point for the predicate compiler; definition of Toplevel
commands code_pred and values.
*)

signature PREDICATE_COMPILE =
sig
  val setup : theory -> theory
  val preprocess : Predicate_Compile_Aux.options -> term -> theory -> theory
  val present_graph : bool Unsynchronized.ref
  val intro_hook : (theory -> thm -> unit) option Unsynchronized.ref
end;

structure Predicate_Compile : PREDICATE_COMPILE =
struct

val present_graph = Unsynchronized.ref false

val intro_hook = Unsynchronized.ref NONE : (theory -> thm -> unit) option Unsynchronized.ref

open Predicate_Compile_Aux;

fun print_intross options thy msg intross =
  if show_intermediate_results options then
    tracing (msg ^ 
      (space_implode "\n" (map 
        (fn (c, intros) => "Introduction rule(s) of " ^ c ^ ":\n" ^
           commas (map (Display.string_of_thm_global thy) intros)) intross)))
  else ()
      
fun print_specs options thy specs =
  if show_intermediate_results options then
    map (fn (c, thms) => "Constant " ^ c ^ " has specification:\n"
      ^ (space_implode "\n" (map (Display.string_of_thm_global thy) thms)) ^ "\n") specs
    |> space_implode "\n" |> tracing
  else ()
fun overload_const thy s = the_default s (Option.map fst (AxClass.inst_of_param thy s))

fun map_specs f specs =
  map (fn (s, ths) => (s, f ths)) specs

fun process_specification options specs thy' =
  let
    val _ = print_step options "Compiling predicates to flat introrules..."
    val specs = map (apsnd (map
      (fn th => if is_equationlike th then Predicate_Compile_Data.normalize_equation thy' th else th))) specs
    val (intross1, thy'') =
      apfst flat (fold_map (Predicate_Compile_Pred.preprocess options) specs thy')
    val _ = print_intross options thy'' "Flattened introduction rules: " intross1
    val _ = print_step options "Replacing functions in introrules..."
    val intross2 =
      if function_flattening options then
        if fail_safe_function_flattening options then
          case try (map_specs (maps (Predicate_Compile_Fun.rewrite_intro thy''))) intross1 of
            SOME intross => intross
          | NONE =>
            (if show_caught_failures options then tracing "Function replacement failed!" else ();
            intross1)
        else map_specs (maps (Predicate_Compile_Fun.rewrite_intro thy'')) intross1
      else
        intross1
    val _ = print_intross options thy'' "Introduction rules with replaced functions: " intross2
    val _ = print_step options "Introducing new constants for abstractions at higher-order argument positions..."
    val (intross3, (new_defs, thy''')) = Predicate_Compile_Pred.flat_higher_order_arguments (intross2, thy'')
    val (new_intross, thy'''')  =
      if not (null new_defs) then
        let
          val _ = print_step options "Recursively obtaining introduction rules for new definitions..."
        in process_specification options new_defs thy''' end
      else ([], thy''')
  in
    (intross3 @ new_intross, thy'''')
  end

fun preprocess_strong_conn_constnames options gr ts thy =
  if forall (fn (Const (c, _)) =>
      Core_Data.is_registered (Proof_Context.init_global thy) c) ts then
    thy
  else
    let
      fun get_specs ts = map_filter (fn t =>
        Term_Graph.get_node gr t |>
        (fn ths => if null ths then NONE else SOME (fst (dest_Const t), ths)))
        ts
      val _ = print_step options ("Preprocessing scc of " ^
        commas (map (Syntax.string_of_term_global thy) ts))
      val (prednames, funnames) = List.partition (fn t => body_type (fastype_of t) = @{typ bool}) ts
      (* untangle recursion by defining predicates for all functions *)
      val _ = print_step options
        ("Compiling functions (" ^ commas (map (Syntax.string_of_term_global thy) funnames) ^
          ") to predicates...")
      val (fun_pred_specs, thy1) =
        (if function_flattening options andalso (not (null funnames)) then
          if fail_safe_function_flattening options then
            case try (Predicate_Compile_Fun.define_predicates (get_specs funnames)) thy of
              SOME (intross, thy) => (intross, thy)
            | NONE => ([], thy)
          else Predicate_Compile_Fun.define_predicates (get_specs funnames) thy
        else ([], thy))
        (*||> Theory.checkpoint*)
      val _ = print_specs options thy1 fun_pred_specs
      val specs = (get_specs prednames) @ fun_pred_specs
      val (intross3, thy2) = process_specification options specs thy1
      val _ = print_intross options thy2 "Introduction rules with new constants: " intross3
      val intross4 = map_specs (maps remove_pointless_clauses) intross3
      val _ = print_intross options thy2 "After removing pointless clauses: " intross4
      val intross5 = map_specs (map (remove_equalities thy2)) intross4
      val _ = print_intross options thy2 "After removing equality premises:" intross5
      val intross6 =
        map (fn (s, ths) => (overload_const thy2 s, map (AxClass.overload thy2) ths)) intross5
      val intross7 = map_specs (map (expand_tuples thy2)) intross6
      val intross8 = map_specs (map (eta_contract_ho_arguments thy2)) intross7
      val _ = case !intro_hook of NONE => () | SOME f => (map_specs (map (f thy2)) intross8; ())
      val _ = print_step options ("Looking for specialisations in " ^ commas (map fst intross8) ^ "...")
      val (intross9, thy3) =
        if specialise options then
          Predicate_Compile_Specialisation.find_specialisations [] intross8 thy2
        else (intross8, thy2)
      val _ = print_intross options thy3 "introduction rules after specialisations: " intross9
      val intross10 = map_specs (map_filter (peephole_optimisation thy3)) intross9
      val _ = print_intross options thy3 "introduction rules before registering: " intross10
      val _ = print_step options "Registering introduction rules..."
      val thy4 = fold Core_Data.register_intros intross10 thy3
    in
      thy4
    end;

fun preprocess options t thy =
  let
    val _ = print_step options "Fetching definitions from theory..."
    val gr = cond_timeit (Config.get_global thy Quickcheck.timing) "preprocess-obtain graph"
          (fn () => Predicate_Compile_Data.obtain_specification_graph options thy t
          |> (fn gr => Term_Graph.restrict (member (op =) (Term_Graph.all_succs gr [t])) gr))
    val _ = if !present_graph then Predicate_Compile_Data.present_graph gr else ()
  in
    cond_timeit (Config.get_global thy Quickcheck.timing) "preprocess-process"
      (fn () => (fold_rev (preprocess_strong_conn_constnames options gr)
        (Term_Graph.strong_conn gr) thy))
  end

datatype proposed_modes = Multiple_Preds of (string * (mode * string option) list) list
  | Single_Pred of (mode * string option) list

fun extract_options lthy (((expected_modes, proposed_modes), (compilation, raw_options)), const) =
  let
    fun chk s = member (op =) raw_options s
    val proposed_modes = case proposed_modes of
          Single_Pred proposed_modes => [(const, proposed_modes)]
        | Multiple_Preds proposed_modes => map
          (apfst (Code.read_const (Proof_Context.theory_of lthy))) proposed_modes
  in
    Options {
      expected_modes = Option.map (pair const) expected_modes,
      proposed_modes = 
        map (apsnd (map fst)) proposed_modes,
      proposed_names =
        maps (fn (predname, ms) => (map_filter
          (fn (m, NONE) => NONE | (m, SOME name) => SOME ((predname, m), name))) ms) proposed_modes,
      show_steps = chk "show_steps",
      show_intermediate_results = chk "show_intermediate_results",
      show_proof_trace = chk "show_proof_trace",
      show_modes = chk "show_modes",
      show_mode_inference = chk "show_mode_inference",
      show_compilation = chk "show_compilation",
      show_caught_failures = false,
      show_invalid_clauses = chk "show_invalid_clauses",
      skip_proof = chk "skip_proof",
      function_flattening = not (chk "no_function_flattening"),
      specialise = chk "specialise",
      fail_safe_function_flattening = false,
      no_topmost_reordering = (chk "no_topmost_reordering"),
      no_higher_order_predicate = [],
      inductify = chk "inductify",
      detect_switches = chk "detect_switches",
      smart_depth_limiting = chk "smart_depth_limiting",
      compilation = compilation
    }
  end

fun code_pred_cmd (((expected_modes, proposed_modes), raw_options), raw_const) lthy =
  let
     val thy = Proof_Context.theory_of lthy
     val const = Code.read_const thy raw_const
     val T = Sign.the_const_type thy const
     val t = Const (const, T)
     val options = extract_options lthy (((expected_modes, proposed_modes), raw_options), const)
  in
    if is_inductify options then
      let
        val lthy' = Local_Theory.background_theory (preprocess options t) lthy
        val const =
          case Predicate_Compile_Fun.pred_of_function (Proof_Context.theory_of lthy') const of
            SOME c => c
          | NONE => const
        val _ = print_step options "Starting Predicate Compile Core..."
      in
        Predicate_Compile_Core.code_pred options const lthy'
      end
    else
      Predicate_Compile_Core.code_pred_cmd options raw_const lthy
  end

val setup = Predicate_Compile_Core.setup


(* Parser for mode annotations *)

fun parse_mode_basic_expr xs =
  (Args.$$$ "i" >> K Input || Args.$$$ "o" >> K Output ||
    Args.$$$ "bool" >> K Bool || Args.$$$ "(" |-- parse_mode_expr --| Args.$$$ ")") xs
and parse_mode_tuple_expr xs =
  (parse_mode_basic_expr --| (Args.$$$ "*" || Args.$$$ "\<times>") -- parse_mode_tuple_expr >> Pair || parse_mode_basic_expr)
    xs
and parse_mode_expr xs =
  (parse_mode_tuple_expr --| (Args.$$$ "=>" || Args.$$$ "\<Rightarrow>") -- parse_mode_expr >> Fun || parse_mode_tuple_expr) xs

val mode_and_opt_proposal = parse_mode_expr --
  Scan.optional (Args.$$$ "as" |-- Parse.xname >> SOME) NONE


val opt_modes =
  Scan.optional (@{keyword "("} |-- Args.$$$ "modes" |-- @{keyword ":"} |--
    (((Parse.enum1 "and" (Parse.xname --| @{keyword ":"} --
        (Parse.enum "," mode_and_opt_proposal))) >> Multiple_Preds)
      || ((Parse.enum "," mode_and_opt_proposal) >> Single_Pred))
    --| @{keyword ")"}) (Multiple_Preds [])

val opt_expected_modes =
  Scan.optional (@{keyword "("} |-- Args.$$$ "expected_modes" |-- @{keyword ":"} |--
    Parse.enum "," parse_mode_expr --| @{keyword ")"} >> SOME) NONE

(* Parser for options *)

val scan_options =
  let
    val scan_bool_option = foldl1 (op ||) (map Args.$$$ bool_options)
    val scan_compilation = foldl1 (op ||) (map (fn (s, c) => Args.$$$ s >> K c) compilation_names)
  in
    Scan.optional (@{keyword "["} |-- Scan.optional scan_compilation Pred
      -- Parse.enum "," scan_bool_option --| @{keyword "]"})
      (Pred, [])
  end

val opt_print_modes =
  Scan.optional (@{keyword "("} |-- Parse.!!! (Scan.repeat1 Parse.xname --| @{keyword ")"})) [];

val opt_mode = (Args.$$$ "_" >> K NONE) || (parse_mode_expr >> SOME)

val opt_param_modes = Scan.optional (@{keyword "["} |-- Args.$$$ "mode" |-- @{keyword ":"} |--
  Parse.enum ", " opt_mode --| @{keyword "]"} >> SOME) NONE

val stats = Scan.optional (Args.$$$ "stats" >> K true) false

val value_options =
  let
    val expected_values = Scan.optional (Args.$$$ "expected" |-- Parse.term >> SOME) NONE
    val scan_compilation =
      Scan.optional
        (foldl1 (op ||)
          (map (fn (s, c) => Args.$$$ s -- Parse.enum "," Parse.int >> (fn (_, ps) => (c, ps)))
            compilation_names))
        (Pred, [])
  in
    Scan.optional
      (@{keyword "["} |-- (expected_values -- stats) -- scan_compilation --| @{keyword "]"})
      ((NONE, false), (Pred, []))
  end

(* code_pred command and values command *)

val _ = Outer_Syntax.local_theory_to_proof "code_pred"
  "prove equations for predicate specified by intro/elim rules"
  Keyword.thy_goal
  (opt_expected_modes -- opt_modes -- scan_options -- Parse.term_group >> code_pred_cmd)

val _ = Outer_Syntax.improper_command "values" "enumerate and print comprehensions" Keyword.diag
  (opt_print_modes -- opt_param_modes -- value_options -- Scan.optional Parse.nat ~1 -- Parse.term
    >> (fn ((((print_modes, param_modes), options), k), t) => Toplevel.keep
        (Predicate_Compile_Core.values_cmd print_modes param_modes options k t)));

end
