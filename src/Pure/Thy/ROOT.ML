(*  Title:      Pure/Thy/ROOT
    ID:         $Id$
    Author:     Sonia Mahjoub / Tobias Nipkow
    Copyright   1992  TU Muenchen

This file builds the theory parser.
It assumes the standard Isabelle environment.
*)

use "scan.ML";
use "parse.ML";
use "syntax.ML";
use "read.ML";


structure Keyword =
    struct
    val alphas =  ["classes", "default", "arities", "types",
                   "consts", "rules", "end", "rules", "mixfix",
                   "infixr", "infixl", "binder", "translations"]

    val symbols = [",", "<", "{", "}", "(", ")", "(*", "*)",
                   "[", "]", "::", "=", "+", "==", "=>", "<="]
    end;

structure Lex     = LexicalFUN (Keyword);
structure Parse   = ParseFUN (Lex);
structure ThySyn  = ThySynFUN (Parse);
structure Readthy = ReadthyFUN (ThySyn);

open Readthy;
