(* Author: Lukas Bulwahn, TU Muenchen

*)
signature PREDICATE_COMPILE =
sig
  val setup : theory -> theory
  val preprocess : Predicate_Compile_Aux.options -> string -> theory -> theory
end;

structure Predicate_Compile : PREDICATE_COMPILE =
struct

(* options *)
val fail_safe_mode = true

open Predicate_Compile_Aux;

val priority = tracing;

(* Some last processing *)

fun remove_pointless_clauses intro =
  if Logic.strip_imp_prems (prop_of intro) = [@{prop "False"}] then
    []
  else [intro]

fun tracing s = ()

fun print_intross options thy msg intross =
  if show_intermediate_results options then
   Output.tracing (msg ^ 
    (space_implode "\n" (map 
      (fn (c, intros) => "Introduction rule(s) of " ^ c ^ ":\n" ^
         commas (map (Display.string_of_thm_global thy) intros)) intross)))
  else ()
      
fun print_specs thy specs =
  map (fn (c, thms) => "Constant " ^ c ^ " has specification:\n"
    ^ (space_implode "\n" (map (Display.string_of_thm_global thy) thms)) ^ "\n") specs

fun map_specs f specs =
  map (fn (s, ths) => (s, f ths)) specs

fun process_specification options specs thy' =
  let
    val _ = print_step options "Compiling predicates to flat introrules..."
    val specs = map (apsnd (map
      (fn th => if is_equationlike th then Predicate_Compile_Data.normalize_equation thy' th else th))) specs
    val (intross1, thy'') = apfst flat (fold_map Predicate_Compile_Pred.preprocess specs thy')
    val _ = print_intross options thy'' "Flattened introduction rules: " intross1
    val _ = print_step options "Replacing functions in introrules..."
    val intross2 =
      if fail_safe_mode then
        case try (map_specs (maps (Predicate_Compile_Fun.rewrite_intro thy''))) intross1 of
          SOME intross => intross
        | NONE => let val _ = warning "Function replacement failed!" in intross1 end
      else map_specs (maps (Predicate_Compile_Fun.rewrite_intro thy'')) intross1
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


fun preprocess_strong_conn_constnames options gr constnames thy =
  let
    val get_specs = map (fn k => (k, Graph.get_node gr k))
    val _ = print_step options ("Preprocessing scc of " ^ commas constnames)
    val (prednames, funnames) = List.partition (is_pred thy) constnames
    (* untangle recursion by defining predicates for all functions *)
    val _ = print_step options
      ("Compiling functions (" ^ commas funnames ^ ") to predicates...")
    val (fun_pred_specs, thy') =
      if not (null funnames) then Predicate_Compile_Fun.define_predicates
      (get_specs funnames) thy else ([], thy)
    val _ = print_specs thy' fun_pred_specs
    val specs = (get_specs prednames) @ fun_pred_specs
    val (intross3, thy''') = process_specification options specs thy'
    val _ = print_intross options thy''' "Introduction rules with new constants: " intross3
    val intross4 = map_specs (maps remove_pointless_clauses) intross3
    val _ = print_intross options thy''' "After removing pointless clauses: " intross4
      (*val intross5 = map (fn s, ths) => ( s, map (AxClass.overload thy''') ths)) intross4*)
    val intross6 = map_specs (map (expand_tuples thy''')) intross4
    val _ = print_intross options thy''' "introduction rules before registering: " intross6
    val _ = print_step options "Registering introduction rules..."
    val thy'''' = fold Predicate_Compile_Core.register_intros intross6 thy'''
  in
    thy''''
  end;

fun preprocess options const thy =
  let
    val _ = print_step options "Fetching definitions from theory..."
    val table = Predicate_Compile_Data.make_const_spec_table thy
    val gr = Predicate_Compile_Data.obtain_specification_graph options thy table const
    val gr = Graph.subgraph (member (op =) (Graph.all_succs gr [const])) gr
  in fold_rev (preprocess_strong_conn_constnames options gr)
    (Graph.strong_conn gr) thy
  end

fun extract_options ((modes, raw_options), const) =
  let
    fun chk s = member (op =) raw_options s
  in
    Options {
      expected_modes = Option.map (pair const) modes,
      show_steps = chk "show_steps",
      show_intermediate_results = chk "show_intermediate_results",
      show_proof_trace = chk "show_proof_trace",
      show_modes = chk "show_modes",
      show_mode_inference = chk "show_mode_inference",
      show_compilation = chk "show_compilation",
      skip_proof = chk "skip_proof",
      inductify = chk "inductify",
      rpred = chk "rpred",
      depth_limited = chk "depth_limited"
    }
  end

fun code_pred_cmd ((modes, raw_options), raw_const) lthy =
  let
     val thy = ProofContext.theory_of lthy
     val const = Code.read_const thy raw_const
     val options = extract_options ((modes, raw_options), const)
  in
    if (is_inductify options) then
      let
        val lthy' = LocalTheory.theory (preprocess options const) lthy
          |> LocalTheory.checkpoint
        val const = case Predicate_Compile_Fun.pred_of_function (ProofContext.theory_of lthy') const of
            SOME c => c
          | NONE => const
        val _ = print_step options "Starting Predicate Compile Core..."
      in
        Predicate_Compile_Core.code_pred options const lthy'
      end
    else
      Predicate_Compile_Core.code_pred_cmd options raw_const lthy
  end

val setup = Predicate_Compile_Fun.setup_oracle #> Predicate_Compile_Core.setup

val bool_options = ["show_steps", "show_intermediate_results", "show_proof_trace", "show_modes",
  "show_mode_inference", "show_compilation", "skip_proof", "inductify", "rpred", "depth_limited"]

local structure P = OuterParse
in

val opt_modes =
  Scan.optional (P.$$$ "(" |-- Args.$$$ "mode" |-- P.$$$ ":" |--
   P.enum1 "," (P.$$$ "[" |-- P.enum "," P.nat --| P.$$$ "]")
  --| P.$$$ ")" >> SOME) NONE

val scan_params =
  let
    val scan_bool_param = foldl1 (op ||) (map Args.$$$ bool_options)
  in
    Scan.optional (P.$$$ "[" |-- P.enum1 "," scan_bool_param --| P.$$$ "]") []
  end

val _ = OuterSyntax.local_theory_to_proof "code_pred"
  "prove equations for predicate specified by intro/elim rules"
  OuterKeyword.thy_goal (opt_modes -- scan_params -- P.term_group >>
    code_pred_cmd)

end

end
