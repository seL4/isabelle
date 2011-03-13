(*  Title:      HOL/Tools/Quickcheck/narrowing_generators.ML
    Author:     Lukas Bulwahn, TU Muenchen

Narrowing-based counterexample generation.
*)

signature NARROWING_GENERATORS =
sig
  val compile_generator_expr:
    Proof.context -> term -> int -> term list option * Quickcheck.report option
  val put_counterexample: (unit -> term list option) -> Proof.context -> Proof.context
  val setup: theory -> theory
end;

structure Narrowing_Generators : NARROWING_GENERATORS =
struct

val target = "Haskell"

(* invocation of Haskell interpreter *)

val narrowing_engine = File.read (Path.explode "~~/src/HOL/Tools/Quickcheck/Narrowing_Engine.hs")

fun exec verbose code =
  ML_Context.exec (fn () => Secure.use_text ML_Env.local_context (0, "generated code") verbose code)

fun value ctxt (get, put, put_ml) (code, value) =
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
          "main = Narrowing_Engine.smallCheck 7 (Code.value ())\n\n" ^
          "}\n"
        val code' = prefix "module Code where {\n\ndata Typerep = Typerep String [Typerep];\n"
          (unprefix "module Code where {" code)
        val _ = File.write code_file code'
        val _ = File.write narrowing_engine_file narrowing_engine
        val _ = File.write main_file main
        val executable = Path.implode (Path.append in_path (Path.basic "isa_lsc"))
        val cmd = getenv "EXEC_GHC" ^ " -fglasgow-exts " ^ 
          (space_implode " " (map Path.implode [code_file, narrowing_engine_file, main_file])) ^
          " -o " ^ executable ^ " && " ^ executable
      in
        bash_output cmd
      end
    val result = Isabelle_System.with_tmp_dir tmp_prefix run
    val output_value = the_default "NONE"
      (try (snd o split_last o filter_out (fn s => s = "") o split_lines o fst) result)
    val ml_code = "\nval _ = Context.set_thread_data (SOME (Context.map_proof (" ^ put_ml
      ^ " (fn () => " ^ output_value ^ ")) (ML_Context.the_generic_context ())))";
    val ctxt' = ctxt
      |> put (fn () => error ("Bad evaluation for " ^ quote put_ml))
      |> Context.proof_map (exec false ml_code);
  in get ctxt' () end;

fun evaluation cookie thy evaluator vs_t args =
  let
    val ctxt = ProofContext.init_global thy;
    val (program_code, value_name) = evaluator vs_t;
    val value_code = space_implode " "
      (value_name :: "()" :: map (enclose "(" ")") args);
  in Exn.interruptible_capture (value ctxt cookie) (program_code, value_code) end;

fun dynamic_value_strict cookie thy postproc t args =
  let
    fun evaluator naming program ((_, vs_ty), t) deps =
      evaluation cookie thy (Code_Target.evaluator thy target naming program deps) (vs_ty, t) args;
  in Exn.release (Code_Thingol.dynamic_value thy (Exn.map_result o postproc) evaluator t) end;

(* counterexample generator *)
  
structure Counterexample = Proof_Data
(
  type T = unit -> term list option
  fun init _ () = error "Counterexample"
)

val put_counterexample =  Counterexample.put
  
fun compile_generator_expr ctxt t size =
  let
    val thy = ProofContext.theory_of ctxt
    fun ensure_testable t =
      Const (@{const_name Quickcheck_Narrowing.ensure_testable}, fastype_of t --> fastype_of t) $ t
    val t = dynamic_value_strict
      (Counterexample.get, Counterexample.put, "Narrowing_Generators.put_counterexample")
      thy (Option.map o map) (ensure_testable t) []
  in
    (t, NONE)
  end;


val setup =
  Context.theory_map
    (Quickcheck.add_generator ("narrowing", compile_generator_expr))
    
end;