(*  Title:      HOL/Tools/Predicate_Compile/predicate_compile_quickcheck.ML
    Author:     Lukas Bulwahn, TU Muenchen

A quickcheck generator based on the predicate compiler.
*)

signature PREDICATE_COMPILE_QUICKCHECK =
sig
  (*val quickcheck : Proof.context -> term -> int -> term list option*)
  val put_pred_result :
    (unit -> int -> int -> int -> int * int -> term list Predicate.pred) ->
      Proof.context -> Proof.context;
  val put_dseq_result :
    (unit -> int -> int -> int * int -> term list DSequence.dseq * (int * int)) ->
      Proof.context -> Proof.context;
  val put_lseq_result :
    (unit -> int -> int -> int * int -> int -> term list Lazy_Sequence.lazy_sequence) ->
      Proof.context -> Proof.context;

  val tracing : bool Unsynchronized.ref;
  val quiet : bool Unsynchronized.ref;
  val quickcheck_compile_term : Predicate_Compile_Aux.compilation -> bool -> bool -> int ->
    Proof.context -> term -> int -> term list option * (bool list * bool);
(*  val test_term : Proof.context -> bool -> int -> int -> int -> int -> term -> *)
  val nrandom : int Unsynchronized.ref;
  val debug : bool Unsynchronized.ref;
  val function_flattening : bool Unsynchronized.ref;
  val no_higher_order_predicate : string list Unsynchronized.ref;
end;

structure Predicate_Compile_Quickcheck : PREDICATE_COMPILE_QUICKCHECK =
struct

open Predicate_Compile_Aux;

structure Pred_Result = Proof_Data (
  type T = unit -> int -> int -> int -> int * int -> term list Predicate.pred
  fun init _ () = error "Pred_Result"
);
val put_pred_result = Pred_Result.put;

structure Dseq_Result = Proof_Data (
  type T = unit -> int -> int -> int * int -> term list DSequence.dseq * (int * int)
  fun init _ () = error "Dseq_Result"
);
val put_dseq_result = Dseq_Result.put;

structure Lseq_Result = Proof_Data (
  type T = unit -> int -> int -> int * int -> int -> term list Lazy_Sequence.lazy_sequence
  fun init _ () = error "Lseq_Result"
);
val put_lseq_result = Lseq_Result.put;

val tracing = Unsynchronized.ref false;

val quiet = Unsynchronized.ref true;

val target = "Quickcheck"

val nrandom = Unsynchronized.ref 3;

val debug = Unsynchronized.ref false;

val function_flattening = Unsynchronized.ref true;

val no_higher_order_predicate = Unsynchronized.ref ([] : string list);

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
  no_topmost_reordering = true
}


fun set_function_flattening b
  (Options { expected_modes = e_m, proposed_modes = p_m, proposed_names = p_n, show_steps = s_s,
    show_intermediate_results = s_ir, show_proof_trace = s_pt, show_modes = s_m,
    show_mode_inference = s_mi, show_compilation = s_c, show_caught_failures = s_cf,
    show_invalid_clauses = s_ic, skip_proof = s_p,
    compilation = c, inductify = i, specialise = sp, detect_switches = ds, function_flattening = f_f, 
    fail_safe_function_flattening = fs_ff, no_higher_order_predicate = no_ho,
    no_topmost_reordering = re}) =
  (Options { expected_modes = e_m, proposed_modes = p_m, proposed_names = p_n, show_steps = s_s,
    show_intermediate_results = s_ir, show_proof_trace = s_pt, show_modes = s_m,
    show_mode_inference = s_mi, show_compilation = s_c, show_caught_failures = s_cf,
    show_invalid_clauses = s_ic, skip_proof = s_p,
    compilation = c, inductify = i, specialise = sp, detect_switches = ds, function_flattening = b,
    fail_safe_function_flattening = fs_ff, no_higher_order_predicate = no_ho,
    no_topmost_reordering = re})

fun set_fail_safe_function_flattening b
  (Options { expected_modes = e_m, proposed_modes = p_m, proposed_names = p_n, show_steps = s_s,
    show_intermediate_results = s_ir, show_proof_trace = s_pt, show_modes = s_m,
    show_mode_inference = s_mi, show_compilation = s_c, show_caught_failures = s_cf,
    show_invalid_clauses = s_ic, skip_proof = s_p,
    compilation = c, inductify = i, specialise = sp, detect_switches = ds, function_flattening = f_f, 
    fail_safe_function_flattening = fs_ff, no_higher_order_predicate = no_ho,
    no_topmost_reordering = re}) =
  (Options { expected_modes = e_m, proposed_modes = p_m, proposed_names = p_n, show_steps = s_s,
    show_intermediate_results = s_ir, show_proof_trace = s_pt, show_modes = s_m,
    show_mode_inference = s_mi, show_compilation = s_c, show_caught_failures = s_cf,
    show_invalid_clauses = s_ic, skip_proof = s_p,
    compilation = c, inductify = i, specialise = sp, detect_switches = ds, function_flattening = f_f,
    fail_safe_function_flattening = b, no_higher_order_predicate = no_ho,
    no_topmost_reordering = re})

fun set_no_higher_order_predicate ss
  (Options { expected_modes = e_m, proposed_modes = p_m, proposed_names = p_n, show_steps = s_s,
    show_intermediate_results = s_ir, show_proof_trace = s_pt, show_modes = s_m,
    show_mode_inference = s_mi, show_compilation = s_c, show_caught_failures = s_cf,
    show_invalid_clauses = s_ic, skip_proof = s_p,
    compilation = c, inductify = i, specialise = sp, detect_switches = ds, function_flattening = f_f, 
    fail_safe_function_flattening = fs_ff, no_higher_order_predicate = no_ho,
    no_topmost_reordering = re}) =
  (Options { expected_modes = e_m, proposed_modes = p_m, proposed_names = p_n, show_steps = s_s,
    show_intermediate_results = s_ir, show_proof_trace = s_pt, show_modes = s_m,
    show_mode_inference = s_mi, show_compilation = s_c, show_caught_failures = s_cf,
    show_invalid_clauses = s_ic, skip_proof = s_p,
    compilation = c, inductify = i, specialise = sp, detect_switches = ds, function_flattening = f_f,
    fail_safe_function_flattening = fs_ff, no_higher_order_predicate = ss, no_topmost_reordering = re})


fun get_options () = 
  set_no_higher_order_predicate (!no_higher_order_predicate)
    (set_function_flattening (!function_flattening)
      (if !debug then debug_options else options))

val mk_predT = Predicate_Compile_Aux.mk_predT PredicateCompFuns.compfuns
val mk_return' = Predicate_Compile_Aux.mk_single PredicateCompFuns.compfuns
val mk_bind' = Predicate_Compile_Aux.mk_bind PredicateCompFuns.compfuns

val mk_randompredT = Predicate_Compile_Aux.mk_predT RandomPredCompFuns.compfuns
val mk_return = Predicate_Compile_Aux.mk_single RandomPredCompFuns.compfuns
val mk_bind = Predicate_Compile_Aux.mk_bind RandomPredCompFuns.compfuns

val mk_new_randompredT = Predicate_Compile_Aux.mk_predT New_Pos_Random_Sequence_CompFuns.compfuns
val mk_new_return = Predicate_Compile_Aux.mk_single New_Pos_Random_Sequence_CompFuns.compfuns
val mk_new_bind = Predicate_Compile_Aux.mk_bind New_Pos_Random_Sequence_CompFuns.compfuns

fun mk_split_lambda [] t = Abs ("u", HOLogic.unitT, t)
  | mk_split_lambda [x] t = lambda x t
  | mk_split_lambda xs t =
  let
    fun mk_split_lambda' (x::y::[]) t = HOLogic.mk_split (lambda x (lambda y t))
      | mk_split_lambda' (x::xs) t = HOLogic.mk_split (lambda x (mk_split_lambda' xs t))
  in
    mk_split_lambda' xs t
  end;

fun strip_imp_prems (Const(@{const_name HOL.implies}, _) $ A $ B) = A :: strip_imp_prems B
  | strip_imp_prems _ = [];

fun strip_imp_concl (Const(@{const_name HOL.implies}, _) $ A $ B) = strip_imp_concl B
  | strip_imp_concl A = A : term;

fun strip_horn A = (strip_imp_prems A, strip_imp_concl A);

fun cpu_time description f =
  let
    val start = start_timing ()
    val result = Exn.capture f ()
    val time = Time.toMilliseconds (#cpu (end_timing start))
  in (Exn.release result, (description, time)) end

fun compile_term compilation options ctxt t =
  let
    val thy = Theory.copy (ProofContext.theory_of ctxt)
    val (vs, t') = strip_abs t
    val vs' = Variable.variant_frees ctxt [] vs
    val t'' = subst_bounds (map Free (rev vs'), t')
    val (prems, concl) = strip_horn t''
    val constname = "pred_compile_quickcheck"
    val full_constname = Sign.full_bname thy constname
    val constT = map snd vs' ---> @{typ bool}
    val thy1 = Sign.add_consts_i [(Binding.name constname, constT, NoSyn)] thy
    val const = Const (full_constname, constT)
    val t = Logic.list_implies
      (map HOLogic.mk_Trueprop (prems @ [HOLogic.mk_not concl]),
       HOLogic.mk_Trueprop (list_comb (Const (full_constname, constT), map Free vs')))
    val tac = fn _ => Skip_Proof.cheat_tac thy1
    val intro = Goal.prove (ProofContext.init_global thy1) (map fst vs') [] t tac
    val thy2 = Context.theory_map (Predicate_Compile_Alternative_Defs.add_thm intro) thy1
    val (thy3, preproc_time) = cpu_time "predicate preprocessing"
        (fn () => Predicate_Compile.preprocess options const thy2)
    val (thy4, core_comp_time) = cpu_time "random_dseq core compilation"
        (fn () =>
          case compilation of
            Pos_Random_DSeq =>
              Predicate_Compile_Core.add_random_dseq_equations options [full_constname] thy3
          | New_Pos_Random_DSeq =>
              Predicate_Compile_Core.add_new_random_dseq_equations options [full_constname] thy3
          (*| Depth_Limited_Random =>
              Predicate_Compile_Core.add_depth_limited_random_equations options [full_constname] thy3*))
    (*val _ = Predicate_Compile_Core.print_all_modes compilation thy4*)
    val _ = Output.tracing ("Preprocessing time: " ^ string_of_int (snd preproc_time))
    val _ = Output.tracing ("Core compilation time: " ^ string_of_int (snd core_comp_time))
    val ctxt4 = ProofContext.init_global thy4
    val modes = Predicate_Compile_Core.modes_of compilation ctxt4 full_constname
    val output_mode = fold_rev (curry Fun) (map (K Output) (binder_types constT)) Bool
    val prog =
      if member eq_mode modes output_mode then
        let
          val name = Predicate_Compile_Core.function_name_of compilation ctxt4
            full_constname output_mode
          val T = 
            case compilation of
              Pos_Random_DSeq => mk_randompredT (HOLogic.mk_tupleT (map snd vs'))
            | New_Pos_Random_DSeq => mk_new_randompredT (HOLogic.mk_tupleT (map snd vs'))
            | Depth_Limited_Random =>
              [@{typ code_numeral}, @{typ code_numeral}, @{typ code_numeral},
              @{typ "code_numeral * code_numeral"}] ---> mk_predT (HOLogic.mk_tupleT (map snd vs'))
        in
          Const (name, T)
        end
      else error ("Predicate Compile Quickcheck failed: " ^ commas (map string_of_mode modes))
    val qc_term =
      case compilation of
          Pos_Random_DSeq => mk_bind (prog,
            mk_split_lambda (map Free vs') (mk_return (HOLogic.mk_list @{typ term}
            (map2 HOLogic.mk_term_of (map snd vs') (map Free vs')))))
        | New_Pos_Random_DSeq => mk_new_bind (prog,
            mk_split_lambda (map Free vs') (mk_new_return (HOLogic.mk_list @{typ term}
            (map2 HOLogic.mk_term_of (map snd vs') (map Free vs')))))
        | Depth_Limited_Random => fold_rev (curry absdummy)
            [@{typ code_numeral}, @{typ code_numeral}, @{typ code_numeral},
             @{typ "code_numeral * code_numeral"}]
            (mk_bind' (list_comb (prog, map Bound (3 downto 0)),
            mk_split_lambda (map Free vs') (mk_return' (HOLogic.mk_list @{typ term}
            (map2 HOLogic.mk_term_of (map snd vs') (map Free vs'))))))
    val prog =
      case compilation of
        Pos_Random_DSeq =>
          let
            val compiled_term =
              Code_Runtime.value (SOME target) (Dseq_Result.get, put_dseq_result, "Predicate_Compile_Quickcheck.put_dseq_result")
                (fn proc => fn g => fn n => fn size => fn s => g n size s |>> (DSequence.map o map) proc)
                thy4 qc_term []
          in
            (fn size => fn nrandom => fn depth =>
              Option.map fst (DSequence.yield
                (compiled_term nrandom size |> Random_Engine.run) depth true))
          end
      | New_Pos_Random_DSeq =>
          let
            val compiled_term =
              Code_Runtime.value (SOME target)
                (Lseq_Result.get, put_lseq_result, "Predicate_Compile_Quickcheck.put_lseq_result")
                (fn proc => fn g => fn nrandom => fn size => fn s => fn depth =>
                  g nrandom size s depth |> (Lazy_Sequence.mapa o map) proc)
                  thy4 qc_term []
          in
            fn size => fn nrandom => fn depth => Option.map fst (Lazy_Sequence.yield 
               (
               let
                 val seed = Random_Engine.next_seed ()
               in compiled_term nrandom size seed depth end))
          end
      | Depth_Limited_Random =>
          let
            val compiled_term = Code_Runtime.value (SOME target)
              (Pred_Result.get, put_pred_result, "Predicate_Compile_Quickcheck.put_pred_result")
                (fn proc => fn g => fn depth => fn nrandom => fn size => fn seed =>
                  g depth nrandom size seed |> (Predicate.map o map) proc)
                thy4 qc_term []
          in
            fn size => fn nrandom => fn depth => Option.map fst (Predicate.yield 
              (compiled_term depth nrandom size (Random_Engine.run (fn s => (s, s)))))
          end
  in
    prog
  end

fun try_upto quiet f i =
  let
    fun try' j =
      if j <= i then
        let
          val _ = if quiet then () else priority ("Executing depth " ^ string_of_int j)
        in
          case f j handle Match => (if quiet then ()
             else warning "Exception Match raised during quickcheck"; NONE)
          of NONE => try' (j + 1) | SOME q => SOME q
        end
      else
        NONE
  in
    try' 0
  end

(* quickcheck interface functions *)

fun compile_term' compilation options depth ctxt t =
  let
    val c = compile_term compilation options ctxt t
    val dummy_report = ([], false)
  in
    fn size => (try_upto (!quiet) (c size (!nrandom)) depth, dummy_report)
  end

fun quickcheck_compile_term compilation function_flattening fail_safe_function_flattening depth =
  let
     val options =
       set_fail_safe_function_flattening fail_safe_function_flattening
         (set_function_flattening function_flattening (get_options ()))
  in
    compile_term' compilation options depth
  end

end;
