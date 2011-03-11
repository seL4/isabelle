(*  Title:      HOL/Tools/LSC/lazysmallcheck.ML
    Author:     Lukas Bulwahn, TU Muenchen

Prototypic implementation to invoke lazysmallcheck in Isabelle

*)

signature LAZYSMALLCHECK =
sig
  val compile_generator_expr:
    Proof.context -> term -> int -> term list option * Quickcheck.report option
  val put_counterexample: (unit -> term list option) -> Proof.context -> Proof.context
  val setup: theory -> theory
end;

structure Lazysmallcheck : LAZYSMALLCHECK =
struct

(* invocation of Haskell interpreter *)

val lsc_module = File.read (Path.explode "~~/src/HOL/Tools/LSC/LazySmallCheck.hs")

fun exec verbose code =
  ML_Context.exec (fn () => Secure.use_text ML_Env.local_context (0, "generated code") verbose code)

fun value ctxt (get, put, put_ml) (code, value) =
  let
    val tmp_prefix = "LSC"
    fun make_cmd executable files =
      getenv "EXEC_GHC" ^ " -fglasgow-exts " ^ (space_implode " " (map Path.implode files)) ^
        " -o " ^ executable ^ " && " ^ executable
    fun run in_path = 
      let
        val code_file = Path.append in_path (Path.basic "Code.hs")
        val lsc_file = Path.append in_path (Path.basic "LazySmallCheck.hs")
        val main_file = Path.append in_path (Path.basic "Main.hs")
        val main = "module Main where {\n\n" ^
          "import LazySmallCheck;\n" ^
          "import Code;\n\n" ^
          "main = LazySmallCheck.smallCheck 7 (Code.value ())\n\n" ^
          "}\n"
        val code' = prefix "module Code where {\n\ndata Typerep = Typerep String [Typerep];\n"
          (unprefix "module Code where {" code)
        val _ = File.write code_file code'
        val _ = File.write lsc_file lsc_module
        val _ = File.write main_file main
        val executable = Path.implode (Path.append in_path (Path.basic "isa_lsc"))
        val cmd = make_cmd executable [code_file, lsc_file, main_file]
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
      evaluation cookie thy (Code_Target.evaluator thy "Haskell" naming program deps) (vs_ty, t) args;
  in Exn.release (Code_Thingol.dynamic_value thy (Exn.map_result o postproc) evaluator t) end;

(* counterexample generator *)
  
structure Lazysmallcheck_Result = Proof_Data
(
  type T = unit -> term list option
  fun init _ () = error "Lazysmallcheck_Result"
)

val put_counterexample = Lazysmallcheck_Result.put
  
fun compile_generator_expr ctxt t size =
  let
    val thy = ProofContext.theory_of ctxt
    fun ensure_testable t =
      Const (@{const_name LSC.ensure_testable}, fastype_of t --> fastype_of t) $ t
    val t = dynamic_value_strict
      (Lazysmallcheck_Result.get, Lazysmallcheck_Result.put, "Lazysmallcheck.put_counterexample")
      thy (Option.map o map) (ensure_testable t) []
  in
    (t, NONE)
  end;


val setup =
  Context.theory_map
    (Quickcheck.add_generator ("lazy_exhaustive", compile_generator_expr))
    
end;