(*  Title:      Pure/Syntax/ROOT.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

This file builds the syntax module.
*)

(*generic modules*)
use "pretty.ML";
use "scan.ML";
use "source.ML";
use "symbol.ML";

(*actual syntax module*)
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

(*hiding: only the most basic features are opened*)
structure BasicSyntax: BASIC_SYNTAX = Syntax;
open BasicSyntax;
