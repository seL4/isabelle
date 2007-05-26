(*  Title:      HOL/Library/List_Comprehension.thy
    ID:         $Id$
    Author:     Tobias Nipkow
*)

header {* List Comprehension *}

theory List_Comprehension
imports Main
begin

text{* At the moment this theory provides only the input syntax for
list comprehension: @{text"[x. x \<leftarrow> xs, \<dots>]"} rather than
\verb![x| x <- xs, ...]! as in Haskell.

The print translation from internal form to list comprehensions would
be nice. Unfortunately one cannot just turn the translations around
because in the final equality @{text p} occurs twice on the
right-hand side. Due to this restriction, the translation must be hand-coded.

A more substantial extension would be proper theorem proving
support. For example, it would be nice if
@{text"set[f x y. x \<leftarrow> xs, y \<leftarrow> ys, P x y]"}
produced something like
@{term"{z. EX x: set xs. EX y:set ys. P x y \<and> z = f x y}"}.  *}

nonterminals lc_gentest

syntax
"_listcompr" :: "'a \<Rightarrow> idt \<Rightarrow> 'b list \<Rightarrow> lc_gentest \<Rightarrow> 'a list" ("[_ . _ \<leftarrow> __")
"_lc_end" :: "lc_gentest" ("]")
"_lc_gen" :: "idt \<Rightarrow> 'a list \<Rightarrow> lc_gentest \<Rightarrow> lc_gentest" (",_ \<leftarrow> __")
"_lc_test" :: "bool \<Rightarrow> lc_gentest \<Rightarrow> lc_gentest" (",__")


translations
 "[e. p\<leftarrow>xs]" => "map (%p. e) xs"
 "_listcompr e p xs (_lc_gen q ys GT)" =>
  "concat (map (%p. _listcompr e q ys GT) xs)"
 "_listcompr e p xs (_lc_test P GT)" => "_listcompr e p (filter (%p. P) xs) GT"

(*
term "[(x,y). x \<leftarrow> xs, x<y]"
term "[(x,y). x \<leftarrow> xs, x<y, z\<leftarrow>zs]"
term "[(x,y). x \<leftarrow> xs, y \<leftarrow> ys, x<y]"
term "[(x,y,z). x \<leftarrow> xs, y \<leftarrow> ys, z\<leftarrow> zs]"
term "[x. x \<leftarrow> xs, x < a, x > b]"
*)

end
