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

(*This structure is only defined to be compatible with older versions of
  READTHY. Don't use it in newly created theory/ROOT.ML files! Instead
  define a new structure. Otherwise Poly/ML won't save a reference variable
  defined inside the functor. *)
structure Readthy = ReadthyFUN (structure ThySyn = ThySyn);
open Readthy;

