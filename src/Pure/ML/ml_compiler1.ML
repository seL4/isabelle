(*  Title:      Pure/ML/ml_compiler1.ML
    Author:     Makarius

Refined ML use operations for bootstrap.
*)

val {use, use_debug, use_no_debug} =
  let
    val context: ML_Compiler0.context =
     {name_space = ML_Name_Space.global,
      print_depth = NONE,
      here = Position.here oo Position.line_file,
      print = writeln,
      error = error};
  in
    ML_Compiler0.use_operations (fn opt_debug => fn file =>
      Position.setmp_thread_data (Position.file_only file)
        (fn () =>
          ML_Compiler0.use_file context
            {verbose = true, debug = ML_Compiler0.debug_option opt_debug} file
          handle ERROR msg => (writeln msg; error "ML error")) ())
  end;
