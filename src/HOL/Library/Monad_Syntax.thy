(* Author: Alexander Krauss, TU Muenchen
   Author: Christian Sternagel, University of Innsbruck
*)

header {* Monad notation for arbitrary types *}

theory Monad_Syntax
imports Main "~~/src/Tools/Adhoc_Overloading" "~~/src/HOL/Library/More_List"
begin

text {*
  We provide a convenient do-notation for monadic expressions
  well-known from Haskell.  @{const Let} is printed
  specially in do-expressions.
*}

consts
  bind :: "['a, 'b \<Rightarrow> 'c] \<Rightarrow> 'c" (infixr ">>=" 54)

notation (xsymbols)
  bind (infixr "\<guillemotright>=" 54)

notation (latex output)
  bind (infixr "\<bind>" 54)

abbreviation (do_notation)
  bind_do :: "['a, 'b \<Rightarrow> 'c] \<Rightarrow> 'c"
where
  "bind_do \<equiv> bind"

notation (output)
  bind_do (infixr ">>=" 54)

notation (xsymbols output)
  bind_do (infixr "\<guillemotright>=" 54)

notation (latex output)
  bind_do (infixr "\<bind>" 54)

nonterminal do_binds and do_bind

syntax
  "_do_block" :: "do_binds \<Rightarrow> 'a" ("do {//(2  _)//}" [12] 62)
  "_do_bind" :: "[pttrn, 'a] \<Rightarrow> do_bind" ("(_ <-/ _)" 13)
  "_do_let" :: "[pttrn, 'a] \<Rightarrow> do_bind" ("(2let _ =/ _)" [1000, 13] 13)
  "_do_then" :: "'a \<Rightarrow> do_bind" ("_" [14] 13)
  "_do_final" :: "'a \<Rightarrow> do_binds" ("_")
  "_do_cons" :: "[do_bind, do_binds] \<Rightarrow> do_binds" ("_;//_" [13, 12] 12)
  "_thenM" :: "['a, 'b] \<Rightarrow> 'b" (infixr ">>" 54)

syntax (xsymbols)
  "_do_bind"  :: "[pttrn, 'a] \<Rightarrow> do_bind" ("(_ \<leftarrow>/ _)" 13)
  "_thenM" :: "['a, 'b] \<Rightarrow> 'b" (infixr "\<guillemotright>" 54)

syntax (latex output)
  "_thenM" :: "['a, 'b] \<Rightarrow> 'b" (infixr "\<then>" 54)

translations
  "_do_block (_do_cons (_do_then t) (_do_final e))"
    == "CONST bind_do t (\<lambda>_. e)"
  "_do_block (_do_cons (_do_bind p t) (_do_final e))"
    == "CONST bind_do t (\<lambda>p. e)"
  "_do_block (_do_cons (_do_let p t) bs)"
    == "let p = t in _do_block bs"
  "_do_block (_do_cons b (_do_cons c cs))"
    == "_do_block (_do_cons b (_do_final (_do_block (_do_cons c cs))))"
  "_do_cons (_do_let p t) (_do_final s)"
    == "_do_final (let p = t in s)"
  "_do_block (_do_final e)" => "e"
  "(m >> n)" => "(m >>= (\<lambda>_. n))"

setup {*
  Adhoc_Overloading.add_overloaded @{const_name bind}
  #> Adhoc_Overloading.add_variant @{const_name bind} @{const_name Predicate.bind}
  #> Adhoc_Overloading.add_variant @{const_name bind} @{const_name Option.bind}
  #> Adhoc_Overloading.add_variant @{const_name bind} @{const_name More_List.bind}
*}

end
