(*  Title:      HOL/ex/Antiquote.thy
    Author:     Markus Wenzel, TU Muenchen
*)

section \<open>Antiquotations\<close>

theory Antiquote
imports Main
begin

text \<open>A simple example on quote / antiquote in higher-order abstract syntax.\<close>

definition Expr :: "(('a \<Rightarrow> nat) \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> nat"
  where "Expr exp env = exp env"

syntax
  "_Expr" :: "'a \<Rightarrow> 'a"  (\<open>(\<open>notation=\<open>prefix EXPR\<close>\<close>EXPR _)\<close> [1000] 999)
  "_Var" :: "'a \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> nat"  (\<open>(\<open>notation=\<open>prefix VAR\<close>\<close>VAR _)\<close> [1000] 999)

syntax_consts
  "_Expr" \<rightleftharpoons> Expr

parse_translation
  \<open>[Syntax_Trans.quote_antiquote_tr
    \<^syntax_const>\<open>_Expr\<close> \<^syntax_const>\<open>_Var\<close> \<^const_syntax>\<open>Expr\<close>]\<close>

print_translation
  \<open>[Syntax_Trans.quote_antiquote_tr'
    \<^syntax_const>\<open>_Expr\<close> \<^syntax_const>\<open>_Var\<close> \<^const_syntax>\<open>Expr\<close>]\<close>

term "EXPR (a + b + c)"
term "EXPR (a + b + c + VAR x + VAR y + 1)"
term "EXPR (VAR (f w) + VAR x)"

term "Expr (\<lambda>env. env x)"    \<comment> \<open>improper\<close>
term "Expr (\<lambda>env. f env)"
term "Expr (\<lambda>env. f env + env x)"    \<comment> \<open>improper\<close>
term "Expr (\<lambda>env. f env y z)"
term "Expr (\<lambda>env. f env + g y env)"
term "Expr (\<lambda>env. f env + g env y + h a env z)"

end
