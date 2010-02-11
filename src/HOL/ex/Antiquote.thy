(*  Title:      HOL/ex/Antiquote.thy
    Author:     Markus Wenzel, TU Muenchen
*)

header {* Antiquotations *}

theory Antiquote
imports Main
begin

text {*
  A simple example on quote / antiquote in higher-order abstract
  syntax.
*}

syntax
  "_Expr" :: "'a => 'a"    ("EXPR _" [1000] 999)

definition
  var :: "'a => ('a => nat) => nat"    ("VAR _" [1000] 999)
  where "var x env = env x"

definition
  Expr :: "(('a => nat) => nat) => ('a => nat) => nat"
  where "Expr exp env = exp env"

parse_translation {*
  [Syntax.quote_antiquote_tr @{syntax_const "_Expr"} @{const_syntax var} @{const_syntax Expr}]
*}

print_translation {*
  [Syntax.quote_antiquote_tr' @{syntax_const "_Expr"} @{const_syntax var} @{const_syntax Expr}]
*}

term "EXPR (a + b + c)"
term "EXPR (a + b + c + VAR x + VAR y + 1)"
term "EXPR (VAR (f w) + VAR x)"

term "Expr (\<lambda>env. env x)"    -- {* improper *}
term "Expr (\<lambda>env. f env)"
term "Expr (\<lambda>env. f env + env x)"    -- {* improper *}
term "Expr (\<lambda>env. f env y z)"
term "Expr (\<lambda>env. f env + g y env)"
term "Expr (\<lambda>env. f env + g env y + h a env z)"

end
