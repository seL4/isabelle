(*  Title:      HOL/Library/OptionalSugar.thy
    ID:         $Id$
    Author:     Gerwin Klain, Tobias Nipkow
    Copyright   2005 NICTA and TUM
*)
(*<*)
theory OptionalSugar
imports LaTeXsugar
begin

(* append *)
syntax (latex output)
  "appendL" :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "\<^raw:\isacharat>" 65)
translations
  "appendL xs ys" <= "xs @ ys" 
  "appendL (appendL xs ys) zs" <= "appendL xs (appendL ys zs)"


(* aligning equations *)
const_syntax (tab output)
  "op ="  ("(_) \<^raw:}\putisatab\isa{\ >=\<^raw:}\putisatab\isa{> (_)" [50,49] 50)
  "=="  ("(_) \<^raw:}\putisatab\isa{\ >\<equiv>\<^raw:}\putisatab\isa{> (_)")

(* Let *)
translations 
  "_bind (p,DUMMY) e" <= "_bind p (fst e)"
  "_bind (DUMMY,p) e" <= "_bind p (snd e)"

  "_tuple_args x (_tuple_args y z)" ==
    "_tuple_args x (_tuple_arg (_tuple y z))"

  "_bind (Some p) e" <= "_bind p (the e)"
  "_bind (p#DUMMY) e" <= "_bind p (hd e)"
  "_bind (DUMMY#p) e" <= "_bind p (tl e)"


end
(*>*)
