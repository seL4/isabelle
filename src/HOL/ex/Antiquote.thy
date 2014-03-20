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

definition var :: "'a \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> nat"  ("VAR _" [1000] 999)
  where "var x env = env x"

definition Expr :: "(('a \<Rightarrow> nat) \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> nat"
  where "Expr exp env = exp env"

syntax
  "_Expr" :: "'a \<Rightarrow> 'a"  ("EXPR _" [1000] 999)

parse_translation {*
  [Syntax_Trans.quote_antiquote_tr
    @{syntax_const "_Expr"} @{const_syntax var} @{const_syntax Expr}]
*}

print_translation {*
  [Syntax_Trans.quote_antiquote_tr'
    @{syntax_const "_Expr"} @{const_syntax var} @{const_syntax Expr}]
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
