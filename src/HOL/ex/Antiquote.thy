(*  Title:      HOL/ex/Antiquote.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Antiquotations *}

theory Antiquote = Main:

text {*
  A simple example on quote / antiquote in higher-order abstract
  syntax.
*}

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

term "Expr (\<lambda>env. env x)"				(*improper*)
term "Expr (\<lambda>env. f env)"
term "Expr (\<lambda>env. f env + env x)"			(*improper*)
term "Expr (\<lambda>env. f env y z)"
term "Expr (\<lambda>env. f env + g y env)"
term "Expr (\<lambda>env. f env + g env y + h a env z)"

end
