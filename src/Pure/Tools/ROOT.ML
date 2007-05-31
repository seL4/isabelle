(*  Title:      Pure/Tools/ROOT.ML
    ID:         $Id$

Miscellaneous tools and packages for Pure Isabelle.
*)

(*XML syntax for terms and types*)
use "xml_syntax.ML";

(*derived theory and proof elements*)
use "invoke.ML";

(*code generator, 1st generation*)
use "../codegen.ML";

(*code generator, 2nd generation*)
use "codegen_names.ML";
use "codegen_funcgr.ML";
use "codegen_thingol.ML";
use "codegen_serializer.ML";
use "codegen_package.ML";

(*norm-by-eval*)
use "nbe_eval.ML";
use "nbe_codegen.ML";
use "nbe.ML";
