(*  Title:      Pure/ML/ml_compiler2.ML
    Author:     Makarius

Isabelle/ML use operations.
*)

val {use, use_debug, use_no_debug} =
  ML_Compiler0.use_operations (fn opt_debug => fn file =>
    let val flags = ML_Compiler.verbose true (ML_Compiler.debug_flags opt_debug) in
      ML_Context.eval_file flags (Path.explode file)
        handle ERROR msg => (writeln msg; error "ML error")
    end);
