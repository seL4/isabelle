(*  Title:      Pure/Syntax/ROOT.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

This file builds the syntax module.
*)

use "lexicon.ML";
use "token_trans.ML";
use "ast.ML";
use "syn_ext.ML";
use "parser.ML";
use "type_ext.ML";
use "syn_trans.ML";
use "mixfix.ML";
use "printer.ML";
use "syntax.ML";

(*hiding private stuff*)
structure Lexicon = Hidden;
structure TokenTrans = Hidden;
structure Ast = Hidden;
structure SynExt = Hidden;
structure Parser = Hidden;
structure TypeExt = Hidden;
structure SynTrans = Hidden;
structure Mixfix = Hidden;
structure Printer = Hidden;
