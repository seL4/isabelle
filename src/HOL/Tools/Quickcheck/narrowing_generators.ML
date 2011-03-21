(*  Title:      HOL/Tools/Quickcheck/narrowing_generators.ML
    Author:     Lukas Bulwahn, TU Muenchen

Narrowing-based counterexample generation.
*)

signature NARROWING_GENERATORS =
sig
  val compile_generator_expr:
    Proof.context -> term * term list -> int -> term list option * Quickcheck.report option
  val put_counterexample: (unit -> term list option) -> Proof.context -> Proof.context
  val finite_functions : bool Config.T
  val setup: theory -> theory
end;

structure Narrowing_Generators : NARROWING_GENERATORS =
struct

(* configurations *)

val (finite_functions, setup_finite_functions) =
  Attrib.config_bool "quickcheck_finite_functions" (K true)


fun mk_undefined T = Const(@{const_name undefined}, T)

(* narrowing specific names and types *)

exception FUNCTION_TYPE;

val narrowingN = "narrowing";

fun narrowingT T =
  @{typ Quickcheck_Narrowing.code_int} --> Type (@{type_name Quickcheck_Narrowing.cons}, [T])

fun mk_empty T = Const (@{const_name Quickcheck_Narrowing.empty}, narrowingT T)

fun mk_cons c T = Const (@{const_name Quickcheck_Narrowing.cons}, T --> narrowingT T) $ Const (c, T)

fun mk_apply (T, t) (U, u) =
  let
    val (_, U') = dest_funT U
  in
    (U', Const (@{const_name Quickcheck_Narrowing.apply},
      narrowingT U --> narrowingT T --> narrowingT U') $ u $ t)
  end
  
fun mk_sum (t, u) =
  let
    val T = fastype_of t
  in
    Const (@{const_name Quickcheck_Narrowing.sum}, T --> T --> T) $ t $ u
  end

(* creating narrowing instances *)

fun mk_equations descr vs tycos narrowings (Ts, Us) =
  let
    fun mk_call T =
      let
        val narrowing =
          Const (@{const_name "Quickcheck_Narrowing.narrowing_class.narrowing"}, narrowingT T)
      in
        (T, narrowing)
      end
    fun mk_aux_call fTs (k, _) (tyco, Ts) =
      let
        val T = Type (tyco, Ts)
        val _ = if not (null fTs) then raise FUNCTION_TYPE else ()
      in
        (T, nth narrowings k)
      end
    fun mk_consexpr simpleT (c, xs) =
      let
        val Ts = map fst xs
      in snd (fold mk_apply xs (Ts ---> simpleT, mk_cons c (Ts ---> simpleT))) end
    fun mk_rhs exprs = foldr1 mk_sum exprs
    val rhss =
      Datatype_Aux.interpret_construction descr vs
        { atyp = mk_call, dtyp = mk_aux_call }
      |> (map o apfst) Type
      |> map (fn (T, cs) => map (mk_consexpr T) cs)
      |> map mk_rhs
    val lhss = narrowings
    val eqs = map (HOLogic.mk_Trueprop o HOLogic.mk_eq) (lhss ~~ rhss)
  in
    eqs
  end


fun instantiate_narrowing_datatype config descr vs tycos prfx (names, auxnames) (Ts, Us) thy =
  let
    val _ = Datatype_Aux.message config "Creating narrowing generators ...";
    val narrowingsN = map (prefix (narrowingN ^ "_")) (names @ auxnames);
  in
    thy
    |> Class.instantiation (tycos, vs, @{sort narrowing})
    |> (fold_map (fn (name, T) => Local_Theory.define
          ((Binding.conceal (Binding.name name), NoSyn),
            (apfst Binding.conceal Attrib.empty_binding, mk_undefined (narrowingT T)))
        #> apfst fst) (narrowingsN ~~ (Ts @ Us))
      #> (fn (narrowings, lthy) =>
        let
          val eqs_t = mk_equations descr vs tycos narrowings (Ts, Us)
          val eqs = map (fn eq => Goal.prove lthy ["f", "i"] [] eq
            (fn _ => Skip_Proof.cheat_tac (ProofContext.theory_of lthy))) eqs_t
        in
          fold (fn (name, eq) => Local_Theory.note
          ((Binding.conceal (Binding.qualify true prfx
             (Binding.qualify true name (Binding.name "simps"))),
             Code.add_default_eqn_attrib :: map (Attrib.internal o K)
               [Simplifier.simp_add, Nitpick_Simps.add]), [eq]) #> snd) (narrowingsN ~~ eqs) lthy
        end))
    |> Class.prove_instantiation_exit (K (Class.intro_classes_tac []))
  end;

(* testing framework *)

val target = "Haskell"

(* invocation of Haskell interpreter *)

val narrowing_engine = File.read (Path.explode "~~/src/HOL/Tools/Quickcheck/Narrowing_Engine.hs")

fun exec verbose code =
  ML_Context.exec (fn () => Secure.use_text ML_Env.local_context (0, "generated code") verbose code)

fun value ctxt (get, put, put_ml) (code, value) size =
  let
    val tmp_prefix = "Quickcheck_Narrowing"
    fun run in_path = 
      let
        val code_file = Path.append in_path (Path.basic "Code.hs")
        val narrowing_engine_file = Path.append in_path (Path.basic "Narrowing_Engine.hs")
        val main_file = Path.append in_path (Path.basic "Main.hs")
        val main = "module Main where {\n\n" ^
          "import Narrowing_Engine;\n" ^
          "import Code;\n\n" ^
          "main = Narrowing_Engine.smallCheck " ^ string_of_int size ^ " (Code.value ())\n\n" ^
          "}\n"
        val code' = prefix "module Code where {\n\ndata Typerep = Typerep String [Typerep];\n"
          (unprefix "module Code where {" code)
        val _ = File.write code_file code'
        val _ = File.write narrowing_engine_file narrowing_engine
        val _ = File.write main_file main
        val executable = File.shell_path (Path.append in_path (Path.basic "isa_lsc"))
        val cmd = "( exec \"$ISABELLE_GHC\" -fglasgow-exts " ^
          (space_implode " " (map File.shell_path [code_file, narrowing_engine_file, main_file])) ^
          " -o " ^ executable ^ "; ) && " ^ executable
      in
        bash_output cmd
      end
    val result = Isabelle_System.with_tmp_dir tmp_prefix run
    val output_value = the_default "NONE"
      (try (snd o split_last o filter_out (fn s => s = "") o split_lines o fst) result)
      |> translate_string (fn s => if s = "\\" then "\\\\" else s)
    val ml_code = "\nval _ = Context.set_thread_data (SOME (Context.map_proof (" ^ put_ml
      ^ " (fn () => " ^ output_value ^ ")) (ML_Context.the_generic_context ())))";
    val ctxt' = ctxt
      |> put (fn () => error ("Bad evaluation for " ^ quote put_ml))
      |> Context.proof_map (exec false ml_code);
  in get ctxt' () end;

fun evaluation cookie thy evaluator vs_t args size =
  let
    val ctxt = ProofContext.init_global thy;
    val (program_code, value_name) = evaluator vs_t;
    val value_code = space_implode " "
      (value_name :: "()" :: map (enclose "(" ")") args);
  in Exn.interruptible_capture (value ctxt cookie (program_code, value_code)) size end;

fun dynamic_value_strict cookie thy postproc t args size =
  let
    fun evaluator naming program ((_, vs_ty), t) deps =
      evaluation cookie thy (Code_Target.evaluator thy target naming program deps) (vs_ty, t) args size;
  in Exn.release (Code_Thingol.dynamic_value thy (Exn.map_result o postproc) evaluator t) end;

(* counterexample generator *)
  
structure Counterexample = Proof_Data
(
  type T = unit -> term list option
  fun init _ () = error "Counterexample"
)

val put_counterexample = Counterexample.put

fun finitize_functions t =
  let
    val ((names, Ts), t') = apfst split_list (strip_abs t)
    fun mk_eval_ffun dT rT =
      Const (@{const_name "Quickcheck_Narrowing.eval_ffun"}, 
        Type (@{type_name "Quickcheck_Narrowing.ffun"}, [dT, rT]) --> dT --> rT)
    fun mk_eval_cfun dT rT =
      Const (@{const_name "Quickcheck_Narrowing.eval_cfun"}, 
        Type (@{type_name "Quickcheck_Narrowing.cfun"}, [rT]) --> dT --> rT)
    fun eval_function (T as Type (@{type_name fun}, [dT, rT])) =
      let
        val (rt', rT') = eval_function rT
      in
        case dT of
          Type (@{type_name fun}, _) =>
            (fn t => absdummy (dT, rt' (mk_eval_cfun dT rT' $ incr_boundvars 1 t $ Bound 0)),
            Type (@{type_name "Quickcheck_Narrowing.cfun"}, [rT']))
        | _ => (fn t => absdummy (dT, rt' (mk_eval_ffun dT rT' $ incr_boundvars 1 t $ Bound 0)),
            Type (@{type_name "Quickcheck_Narrowing.ffun"}, [dT, rT']))
      end
      | eval_function T = (I, T)
    val (tt, Ts') = split_list (map eval_function Ts)
    val t'' = subst_bounds (map2 (fn f => fn x => f x) (rev tt) (map_index (Bound o fst) Ts), t')
  in
    list_abs (names ~~ Ts', t'')
  end

fun compile_generator_expr ctxt (t, eval_terms) size =
  let
    val thy = ProofContext.theory_of ctxt
    val t' = list_abs_free (Term.add_frees t [], t)
    val t'' = if Config.get ctxt finite_functions then finitize_functions t' else t'
    fun ensure_testable t =
      Const (@{const_name Quickcheck_Narrowing.ensure_testable}, fastype_of t --> fastype_of t) $ t
    val result = dynamic_value_strict
      (Counterexample.get, Counterexample.put, "Narrowing_Generators.put_counterexample")
      thy (Option.map o map) (ensure_testable t'') [] size
  in
    (result, NONE)
  end;


val setup =
  Datatype.interpretation
    (Quickcheck_Common.ensure_sort_datatype (@{sort narrowing}, instantiate_narrowing_datatype))
  #> setup_finite_functions
  #> Context.theory_map
    (Quickcheck.add_generator ("narrowing", compile_generator_expr))
    
end;