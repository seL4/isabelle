(*  Title:      Pure/Tools/ROOT.ML
    ID:         $Id$

Miscellaneous tools and packages for Pure Isabelle.
*)

(*class package*)
use "class_package.ML";

(*code generator, 1st generation*)
use "../codegen.ML";

(*code generator, 2nd generation*)
use "codegen_thingol.ML";
use "codegen_serializer.ML";
use "codegen_package.ML";

(*Steven Obua's evaluator*)
use "am_interpreter.ML";
use "am_compiler.ML";
use "am_util.ML";
use "compute.ML";

(* norm-by-eval *)
use "nbe_eval.ML";
use "nbe_codegen.ML";
