(*  Title:      HOL/Tools/Predicate_Compile/predicate_compile_quickcheck.ML
    Author:     Lukas Bulwahn, TU Muenchen

A quickcheck generator based on the predicate compiler.
*)

signature PREDICATE_COMPILE_QUICKCHECK =
sig
  type seed = Random_Engine.seed
  (*val quickcheck : Proof.context -> term -> int -> term list option*)
  val put_pred_result :
    (unit -> Code_Numeral.natural -> Code_Numeral.natural -> Code_Numeral.natural -> seed ->
      term list Predicate.pred) ->
    Proof.context -> Proof.context
  val put_dseq_result :
    (unit -> Code_Numeral.natural -> Code_Numeral.natural -> seed ->
      term list Limited_Sequence.dseq * seed) ->
    Proof.context -> Proof.context
  val put_lseq_result :
    (unit -> Code_Numeral.natural -> Code_Numeral.natural -> seed -> Code_Numeral.natural ->
      term list Lazy_Sequence.lazy_sequence) ->
    Proof.context -> Proof.context
  val put_new_dseq_result :
    (unit -> Code_Numeral.natural -> term list Lazy_Sequence.lazy_sequence) ->
    Proof.context -> Proof.context
  val put_cps_result : (unit -> Code_Numeral.natural -> (bool * term list) option) ->
    Proof.context -> Proof.context
  val test_goals : (Predicate_Compile_Aux.compilation * bool) ->
    Proof.context -> bool -> (string * typ) list -> (term * term list) list ->
    Quickcheck.result list
  val nrandom : int Unsynchronized.ref
  val debug : bool Unsynchronized.ref
  val no_higher_order_predicate : string list Unsynchronized.ref
end;

structure Predicate_Compile_Quickcheck : PREDICATE_COMPILE_QUICKCHECK =
struct

open Predicate_Compile_Aux;

type seed = Random_Engine.seed;

structure Data = Proof_Data
(
  type T =
    (unit -> Code_Numeral.natural -> Code_Numeral.natural ->
      Code_Numeral.natural -> seed -> term list Predicate.pred) *
    (unit -> Code_Numeral.natural -> Code_Numeral.natural ->
      seed -> term list Limited_Sequence.dseq * seed) *
    (unit -> Code_Numeral.natural -> Code_Numeral.natural ->
      seed -> Code_Numeral.natural -> term list Lazy_Sequence.lazy_sequence) *
    (unit -> Code_Numeral.natural -> term list Lazy_Sequence.lazy_sequence) *
    (unit -> Code_Numeral.natural -> (bool * term list) option);
  val empty: T =
   (fn () => raise Fail "pred_result",
    fn () => raise Fail "dseq_result",
    fn () => raise Fail "lseq_result",
    fn () => raise Fail "new_dseq_result",
    fn () => raise Fail "cps_result");
  fun init _ = empty;
);

val get_pred_result = #1 o Data.get;
val get_dseq_result = #2 o Data.get;
val get_lseq_result = #3 o Data.get;
val get_new_dseq_result = #4 o Data.get;
val get_cps_result = #5 o Data.get;

val put_pred_result = Data.map o @{apply 5(1)} o K;
val put_dseq_result = Data.map o @{apply 5(2)} o K;
val put_lseq_result = Data.map o @{apply 5(3)} o K;
val put_new_dseq_result = Data.map o @{apply 5(4)} o K;
val put_cps_result = Data.map o @{apply 5(5)} o K;

val target = "Quickcheck"

val nrandom = Unsynchronized.ref 3

val debug = Unsynchronized.ref false

val no_higher_order_predicate = Unsynchronized.ref ([] : string list)

val options = Options {
  expected_modes = NONE,
  proposed_modes = [],
  proposed_names = [],
  show_steps = false,
  show_intermediate_results = false,
  show_proof_trace = false,
  show_modes = false,
  show_mode_inference = false,
  show_compilation = false,
  show_caught_failures = false,
  show_invalid_clauses = false,
  skip_proof = false,
  compilation = Random,
  inductify = true,
  specialise = true,
  detect_switches = false,
  function_flattening = true,
  fail_safe_function_flattening = false,
  no_higher_order_predicate = [],
  smart_depth_limiting = true,
  no_topmost_reordering = false
}

val debug_options = Options {
  expected_modes = NONE,
  proposed_modes = [],
  proposed_names = [],
  show_steps = true,
  show_intermediate_results = true,
  show_proof_trace = false,
  show_modes = true,
  show_mode_inference = true,
  show_compilation = false,
  show_caught_failures = true,
  show_invalid_clauses = false,
  skip_proof = false,
  compilation = Random,
  inductify = true,
  specialise = true,
  detect_switches = false,
  function_flattening = true,
  fail_safe_function_flattening = false,
  no_higher_order_predicate = [],
  smart_depth_limiting = true,
  no_topmost_reordering = true
}


fun set_function_flattening b
  (Options { expected_modes = e_m, proposed_modes = p_m, proposed_names = p_n, show_steps = s_s,
    show_intermediate_results = s_ir, show_proof_trace = s_pt, show_modes = s_m,
    show_mode_inference = s_mi, show_compilation = s_c, show_caught_failures = s_cf,
    show_invalid_clauses = s_ic, skip_proof = s_p,
    compilation = c, inductify = i, specialise = sp, detect_switches = ds, function_flattening = _,
    fail_safe_function_flattening = fs_ff, no_higher_order_predicate = no_ho,
    smart_depth_limiting = sm_dl, no_topmost_reordering = re}) =
  (Options { expected_modes = e_m, proposed_modes = p_m, proposed_names = p_n, show_steps = s_s,
    show_intermediate_results = s_ir, show_proof_trace = s_pt, show_modes = s_m,
    show_mode_inference = s_mi, show_compilation = s_c, show_caught_failures = s_cf,
    show_invalid_clauses = s_ic, skip_proof = s_p,
    compilation = c, inductify = i, specialise = sp, detect_switches = ds, function_flattening = b,
    fail_safe_function_flattening = fs_ff, no_higher_order_predicate = no_ho,
    smart_depth_limiting = sm_dl, no_topmost_reordering = re})

fun set_fail_safe_function_flattening b
  (Options { expected_modes = e_m, proposed_modes = p_m, proposed_names = p_n, show_steps = s_s,
    show_intermediate_results = s_ir, show_proof_trace = s_pt, show_modes = s_m,
    show_mode_inference = s_mi, show_compilation = s_c, show_caught_failures = s_cf,
    show_invalid_clauses = s_ic, skip_proof = s_p,
    compilation = c, inductify = i, specialise = sp, detect_switches = ds, function_flattening = f_f,
    fail_safe_function_flattening = _, no_higher_order_predicate = no_ho,
    smart_depth_limiting = sm_dl, no_topmost_reordering = re}) =
  (Options { expected_modes = e_m, proposed_modes = p_m, proposed_names = p_n, show_steps = s_s,
    show_intermediate_results = s_ir, show_proof_trace = s_pt, show_modes = s_m,
    show_mode_inference = s_mi, show_compilation = s_c, show_caught_failures = s_cf,
    show_invalid_clauses = s_ic, skip_proof = s_p,
    compilation = c, inductify = i, specialise = sp, detect_switches = ds, function_flattening = f_f,
    fail_safe_function_flattening = b, no_higher_order_predicate = no_ho,
    smart_depth_limiting = sm_dl, no_topmost_reordering = re})

fun set_no_higher_order_predicate ss
  (Options { expected_modes = e_m, proposed_modes = p_m, proposed_names = p_n, show_steps = s_s,
    show_intermediate_results = s_ir, show_proof_trace = s_pt, show_modes = s_m,
    show_mode_inference = s_mi, show_compilation = s_c, show_caught_failures = s_cf,
    show_invalid_clauses = s_ic, skip_proof = s_p,
    compilation = c, inductify = i, specialise = sp, detect_switches = ds, function_flattening = f_f,
    fail_safe_function_flattening = fs_ff, no_higher_order_predicate = _,
    smart_depth_limiting = sm_dl, no_topmost_reordering = re}) =
  (Options { expected_modes = e_m, proposed_modes = p_m, proposed_names = p_n, show_steps = s_s,
    show_intermediate_results = s_ir, show_proof_trace = s_pt, show_modes = s_m,
    show_mode_inference = s_mi, show_compilation = s_c, show_caught_failures = s_cf,
    show_invalid_clauses = s_ic, skip_proof = s_p,
    compilation = c, inductify = i, specialise = sp, detect_switches = ds, function_flattening = f_f,
    fail_safe_function_flattening = fs_ff, no_higher_order_predicate = ss,
    smart_depth_limiting = sm_dl, no_topmost_reordering = re})


fun get_options () =
  set_no_higher_order_predicate (!no_higher_order_predicate)
    (if !debug then debug_options else options)

val mk_predT = Predicate_Compile_Aux.mk_monadT Predicate_Comp_Funs.compfuns
val mk_return' = Predicate_Compile_Aux.mk_single Predicate_Comp_Funs.compfuns
val mk_bind' = Predicate_Compile_Aux.mk_bind Predicate_Comp_Funs.compfuns

val mk_randompredT = Predicate_Compile_Aux.mk_monadT RandomPredCompFuns.compfuns
val mk_return = Predicate_Compile_Aux.mk_single RandomPredCompFuns.compfuns
val mk_bind = Predicate_Compile_Aux.mk_bind RandomPredCompFuns.compfuns

val mk_new_randompredT =
  Predicate_Compile_Aux.mk_monadT New_Pos_Random_Sequence_CompFuns.depth_unlimited_compfuns
val mk_new_return =
  Predicate_Compile_Aux.mk_single New_Pos_Random_Sequence_CompFuns.depth_unlimited_compfuns
val mk_new_bind =
  Predicate_Compile_Aux.mk_bind New_Pos_Random_Sequence_CompFuns.depth_unlimited_compfuns

val mk_new_dseqT =
  Predicate_Compile_Aux.mk_monadT New_Pos_DSequence_CompFuns.depth_unlimited_compfuns
val mk_gen_return =
  Predicate_Compile_Aux.mk_single New_Pos_DSequence_CompFuns.depth_unlimited_compfuns
val mk_gen_bind =
  Predicate_Compile_Aux.mk_bind New_Pos_DSequence_CompFuns.depth_unlimited_compfuns


val mk_cpsT =
  Predicate_Compile_Aux.mk_monadT Pos_Bounded_CPS_Comp_Funs.compfuns

val mk_split_lambda = HOLogic.tupled_lambda o HOLogic.mk_tuple

fun cpu_time description e =
  let val ({cpu, ...}, result) = Timing.timing e ()
  in (result, (description, Time.toMilliseconds cpu)) end

fun compile_term compilation options ctxt t =
  let
    val t' = fold_rev absfree (Term.add_frees t []) t
    val thy = Proof_Context.theory_of ctxt
    val ((((full_constname, constT), vs'), intro), thy1) =
      Predicate_Compile_Aux.define_quickcheck_predicate t' thy
    val thy2 =
      Context.theory_map (Named_Theorems.add_thm \<^named_theorems>\<open>code_pred_def\<close> intro) thy1
    val (thy3, _) = cpu_time "predicate preprocessing"
        (fn () => Predicate_Compile.preprocess options (Const (full_constname, constT)) thy2)
    val (thy4, _) = cpu_time "random_dseq core compilation"
        (fn () =>
          case compilation of
            Pos_Random_DSeq =>
              Predicate_Compile_Core.add_random_dseq_equations options [full_constname] thy3
          | New_Pos_Random_DSeq =>
              Predicate_Compile_Core.add_new_random_dseq_equations options [full_constname] thy3
          | Pos_Generator_DSeq =>
              Predicate_Compile_Core.add_generator_dseq_equations options [full_constname] thy3
          | Pos_Generator_CPS =>
               Predicate_Compile_Core.add_generator_cps_equations options [full_constname] thy3
          (*| Depth_Limited_Random =>
              Predicate_Compile_Core.add_depth_limited_random_equations options [full_constname] thy3*))
    (*val _ = Predicate_Compile_Core.print_all_modes compilation thy4*)
    val ctxt4 = Proof_Context.init_global thy4
    val modes = Core_Data.modes_of compilation ctxt4 full_constname
    val output_mode = fold_rev (curry Fun) (map (K Output) (binder_types constT)) Bool
    val prog =
      if member eq_mode modes output_mode then
        let
          val name = Core_Data.function_name_of compilation ctxt4 full_constname output_mode
          val T =
            (case compilation of
              Pos_Random_DSeq => mk_randompredT (HOLogic.mk_tupleT (map snd vs'))
            | New_Pos_Random_DSeq => mk_new_randompredT (HOLogic.mk_tupleT (map snd vs'))
            | Pos_Generator_DSeq => mk_new_dseqT (HOLogic.mk_tupleT (map snd vs'))
            | Depth_Limited_Random =>
                [\<^typ>\<open>natural\<close>, \<^typ>\<open>natural\<close>, \<^typ>\<open>natural\<close>,
                 \<^typ>\<open>Random.seed\<close>] ---> mk_predT (HOLogic.mk_tupleT (map snd vs'))
            | Pos_Generator_CPS => mk_cpsT (HOLogic.mk_tupleT (map snd vs')))
        in
          Const (name, T)
        end
      else error ("Predicate Compile Quickcheck failed: " ^ commas (map string_of_mode modes))
    fun mk_Some T = Const (\<^const_name>\<open>Option.Some\<close>, T --> Type (\<^type_name>\<open>Option.option\<close>, [T]))
    val qc_term =
      (case compilation of
        Pos_Random_DSeq => mk_bind (prog,
          mk_split_lambda (map Free vs') (mk_return (HOLogic.mk_list \<^typ>\<open>term\<close>
          (map2 HOLogic.mk_term_of (map snd vs') (map Free vs')))))
      | New_Pos_Random_DSeq => mk_new_bind (prog,
          mk_split_lambda (map Free vs') (mk_new_return (HOLogic.mk_list \<^typ>\<open>term\<close>
          (map2 HOLogic.mk_term_of (map snd vs') (map Free vs')))))
      | Pos_Generator_DSeq => mk_gen_bind (prog,
          mk_split_lambda (map Free vs') (mk_gen_return (HOLogic.mk_list \<^typ>\<open>term\<close>
          (map2 HOLogic.mk_term_of (map snd vs') (map Free vs')))))
      | Pos_Generator_CPS => prog $
          mk_split_lambda (map Free vs') (mk_Some \<^typ>\<open>bool * term list\<close> $
          HOLogic.mk_prod (\<^term>\<open>True\<close>, HOLogic.mk_list \<^typ>\<open>term\<close>
              (map2 HOLogic.mk_term_of (map snd vs') (map Free vs'))))
      | Depth_Limited_Random => fold_rev absdummy
          [\<^typ>\<open>natural\<close>, \<^typ>\<open>natural\<close>, \<^typ>\<open>natural\<close>,
           \<^typ>\<open>Random.seed\<close>]
          (mk_bind' (list_comb (prog, map Bound (3 downto 0)),
          mk_split_lambda (map Free vs') (mk_return' (HOLogic.mk_list \<^typ>\<open>term\<close>
          (map2 HOLogic.mk_term_of (map snd vs') (map Free vs')))))))
    val prog =
      case compilation of
        Pos_Random_DSeq =>
          let
            val compiled_term =
              Code_Runtime.dynamic_value_strict
                (get_dseq_result, put_dseq_result, "Predicate_Compile_Quickcheck.put_dseq_result")
                (Proof_Context.init_global thy4) (SOME target)
                (fn proc => fn g => fn n => fn size => fn s =>
                  g n size s |>> (Limited_Sequence.map o map) proc)
                qc_term []
          in
            (fn size => fn nrandom => fn depth =>
              Option.map fst (Limited_Sequence.yield
                (compiled_term nrandom size |> Random_Engine.run) depth true))
          end
      | New_Pos_Random_DSeq =>
          let
            val compiled_term =
              Code_Runtime.dynamic_value_strict
                (get_lseq_result, put_lseq_result, "Predicate_Compile_Quickcheck.put_lseq_result")
                (Proof_Context.init_global thy4) (SOME target)
                (fn proc => fn g => fn nrandom => fn size => fn s => fn depth =>
                  g nrandom size s depth |> (Lazy_Sequence.map o map) proc)
                  qc_term []
          in
            fn size => fn nrandom => fn depth => Option.map fst (Lazy_Sequence.yield
               (
               let
                 val seed = Random_Engine.next_seed ()
               in compiled_term nrandom size seed depth end))
          end
      | Pos_Generator_DSeq =>
          let
            val compiled_term =
              Code_Runtime.dynamic_value_strict
                (get_new_dseq_result, put_new_dseq_result,
                  "Predicate_Compile_Quickcheck.put_new_dseq_result")
                (Proof_Context.init_global thy4) (SOME target)
                (fn proc => fn g => fn depth => g depth |> (Lazy_Sequence.map o map) proc)
                qc_term []
          in
            fn size => fn nrandom => fn depth =>
              Option.map fst (Lazy_Sequence.yield (compiled_term depth))
          end
      | Pos_Generator_CPS =>
          let
            val compiled_term =
              Code_Runtime.dynamic_value_strict
                (get_cps_result, put_cps_result, "Predicate_Compile_Quickcheck.put_cps_result")
                (Proof_Context.init_global thy4) (SOME target)
                (fn proc => fn g => fn depth => g depth |> Option.map (apsnd (map proc)))
                qc_term []
          in
            fn _ => fn _ => Option.map snd o compiled_term
          end
       | Depth_Limited_Random =>
          let
            val compiled_term = Code_Runtime.dynamic_value_strict
              (get_pred_result, put_pred_result, "Predicate_Compile_Quickcheck.put_pred_result")
                (Proof_Context.init_global thy4) (SOME target)
                  (fn proc => fn g => fn depth => fn nrandom => fn size => fn seed =>
                  g depth nrandom size seed |> (Predicate.map o map) proc)
                qc_term []
          in
            fn size => fn nrandom => fn depth => Option.map fst (Predicate.yield
              (compiled_term depth nrandom size (Random_Engine.run (fn s => (s, s)))))
          end
  in
    prog
  end

fun try_upto_depth ctxt f =
  let
    val max_depth = Config.get ctxt Quickcheck.depth
    fun message s = if Config.get ctxt Quickcheck.quiet then () else writeln s
    fun try' i =
      if i <= max_depth then
        let
          val _ = message ("Depth: " ^ string_of_int i)
          val (result, time) =
            cpu_time ("Depth " ^ string_of_int i) (fn () =>
              f i handle Match => (if Config.get ctxt Quickcheck.quiet then ()
                    else warning "Exception Match raised during quickcheck"; NONE))
         val _ = if Config.get ctxt Quickcheck.timing then
           message (fst time ^ ": " ^ string_of_int (snd time) ^ " ms") else ()
        in
          (case result of NONE => try' (i + 1) | SOME q => SOME q)
        end
      else NONE
  in
    try' 0
  end


(* quickcheck interface functions *)

fun compile_term' compilation options ctxt (t, _) =
  let
    val size = Config.get ctxt Quickcheck.size
    val c = compile_term compilation options ctxt t
    val counterexample = try_upto_depth ctxt (c (Code_Numeral.natural_of_integer size)
      (Code_Numeral.natural_of_integer (!nrandom)) o Code_Numeral.natural_of_integer)
  in
    Quickcheck.Result
      {counterexample =
        Option.map (pair true o (curry (op ~~)) (Term.add_free_names t [])) counterexample,
       evaluation_terms = Option.map (K []) counterexample, timings = [], reports = []}
  end

fun quickcheck_compile_term compilation function_flattening fail_safe_function_flattening =
  let
     val options =
       set_fail_safe_function_flattening fail_safe_function_flattening
         (set_function_flattening function_flattening (get_options ()))
  in
    compile_term' compilation options
  end


fun test_goals options ctxt _ insts goals =
  let
    val (compilation, fail_safe_function_flattening) = options
    val function_flattening = Config.get ctxt (Quickcheck.allow_function_inversion)
    val correct_inst_goals = Quickcheck_Common.instantiate_goals ctxt insts goals
    val test_term =
      quickcheck_compile_term compilation function_flattening fail_safe_function_flattening
  in
    Quickcheck_Common.collect_results (test_term ctxt)
      (maps (map snd) correct_inst_goals) []
  end

val smart_exhaustive_active =
  Attrib.setup_config_bool \<^binding>\<open>quickcheck_smart_exhaustive_active\<close> (K true)
val smart_slow_exhaustive_active =
  Attrib.setup_config_bool \<^binding>\<open>quickcheck_slow_smart_exhaustive_active\<close> (K false)

val _ =
  Theory.setup
   (Exhaustive_Generators.setup_exhaustive_datatype_interpretation #>
    Context.theory_map (Quickcheck.add_tester ("smart_exhaustive",
      (smart_exhaustive_active, test_goals (Predicate_Compile_Aux.Pos_Generator_CPS, false)))) #>
    Context.theory_map (Quickcheck.add_tester ("smart_slow_exhaustive",
      (smart_slow_exhaustive_active, test_goals (Predicate_Compile_Aux.Pos_Generator_DSeq, false)))))

end
