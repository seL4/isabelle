(*  Title:      HOL/Library/Monad_Syntax.thy
    Author:     Alexander Krauss, TU Muenchen
    Author:     Christian Sternagel, University of Innsbruck
*)

section \<open>Monad notation for arbitrary types\<close>

theory Monad_Syntax
  imports Adhoc_Overloading
begin

text \<open>
We provide a convenient do-notation for monadic expressions well-known from Haskell.
\<^const>\<open>Let\<close> is printed specially in do-expressions.
\<close>

consts
  bind :: "'a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'd" (infixl "\<bind>" 54)

notation (ASCII)
  bind (infixl ">>=" 54)


abbreviation (do_notation)
  bind_do :: "'a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'd"
  where "bind_do \<equiv> bind"

notation (output)
  bind_do (infixl "\<bind>" 54)

notation (ASCII output)
  bind_do (infixl ">>=" 54)


nonterminal do_binds and do_bind
syntax
  "_do_block" :: "do_binds \<Rightarrow> 'a" ("do {//(2  _)//}" [12] 62)
  "_do_bind"  :: "[pttrn, 'a] \<Rightarrow> do_bind" ("(2_ \<leftarrow>/ _)" 13)
  "_do_let" :: "[pttrn, 'a] \<Rightarrow> do_bind" ("(2let _ =/ _)" [1000, 13] 13)
  "_do_then" :: "'a \<Rightarrow> do_bind" ("_" [14] 13)
  "_do_final" :: "'a \<Rightarrow> do_binds" ("_")
  "_do_cons" :: "[do_bind, do_binds] \<Rightarrow> do_binds" ("_;//_" [13, 12] 12)
  "_thenM" :: "['a, 'b] \<Rightarrow> 'c" (infixl "\<then>" 54)

syntax (ASCII)
  "_do_bind" :: "[pttrn, 'a] \<Rightarrow> do_bind" ("(2_ <-/ _)" 13)
  "_thenM" :: "['a, 'b] \<Rightarrow> 'c" (infixl ">>" 54)

syntax_consts
  "_do_block" "_do_cons" \<rightleftharpoons> bind_do and
  "_do_bind" "_thenM" \<rightleftharpoons> bind and
  "_do_let" \<rightleftharpoons> Let

translations
  "_do_block (_do_cons (_do_then t) (_do_final e))"
    \<rightleftharpoons> "CONST bind_do t (\<lambda>_. e)"
  "_do_block (_do_cons (_do_bind p t) (_do_final e))"
    \<rightleftharpoons> "CONST bind_do t (\<lambda>p. e)"
  "_do_block (_do_cons (_do_let p t) bs)"
    \<rightleftharpoons> "let p = t in _do_block bs"
  "_do_block (_do_cons b (_do_cons c cs))"
    \<rightleftharpoons> "_do_block (_do_cons b (_do_final (_do_block (_do_cons c cs))))"
  "_do_cons (_do_let p t) (_do_final s)"
    \<rightleftharpoons> "_do_final (let p = t in s)"
  "_do_block (_do_final e)" \<rightharpoonup> "e"
  "(m \<then> n)" \<rightharpoonup> "(m \<bind> (\<lambda>_. n))"

adhoc_overloading
  bind Set.bind Predicate.bind Option.bind List.bind

end
