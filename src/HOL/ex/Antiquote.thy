(*  Title:      HOL/ex/Antiquote.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Simple quote / antiquote example.
*)

theory Antiquote = Main:

syntax
  "_Expr" :: "'a => 'a"				("EXPR _" [1000] 999)

constdefs
  var :: "'a => ('a => nat) => nat"		("VAR _" [1000] 999)
  "var x env == env x"

  Expr :: "(('a => nat) => nat) => ('a => nat) => nat"
  "Expr exp env == exp env"

parse_translation {* [Syntax.quote_antiquote_tr "_Expr" "var" "Expr"] *}
print_translation {* [Syntax.quote_antiquote_tr' "_Expr" "var" "Expr"] *}

term "EXPR (a + b + c)"
term "EXPR (a + b + c + VAR x + VAR y + 1)"
term "EXPR (VAR (f w) + VAR x)"

term "Expr (%env. env x)"				(*improper*)
term "Expr (%env. f env)"
term "Expr (%env. f env + env x)"			(*improper*)
term "Expr (%env. f env y z)"
term "Expr (%env. f env + g y env)"
term "Expr (%env. f env + g env y + h a env z)"

end

