(*  Title:      HOL/Library/OptionalSugar.thy
    Author:     Gerwin Klain, Tobias Nipkow
    Copyright   2005 NICTA and TUM
*)
(*<*)
theory OptionalSugar
imports LaTeXsugar Complex_Main
begin

(* hiding set *)
translations
  "xs" <= "CONST set xs"

(* hiding numeric conversions - embeddings only *)
translations
  "n" <= "CONST of_nat n"
  "n" <= "CONST int n"
  "n" <= "real n"
  "n" <= "CONST real_of_nat n"
  "n" <= "CONST real_of_int n"
  "n" <= "CONST of_real n"
  "n" <= "CONST complex_of_real n"

(* append *)
syntax (latex output)
  "appendL" :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "\<^raw:\isacharat>" 65)
translations
  "appendL xs ys" <= "xs @ ys" 
  "appendL (appendL xs ys) zs" <= "appendL xs (appendL ys zs)"


(* deprecated, use thm_style instead, will be removed *)
(* aligning equations *)
notation (tab output)
  "op ="  ("(_) \<^raw:}\putisatab\isa{\ >=\<^raw:}\putisatab\isa{> (_)" [50,49] 50) and
  "=="  ("(_) \<^raw:}\putisatab\isa{\ >\<equiv>\<^raw:}\putisatab\isa{> (_)")

(* Let *)
translations 
  "_bind (p,DUMMY) e" <= "_bind p (CONST fst e)"
  "_bind (DUMMY,p) e" <= "_bind p (CONST snd e)"

  "_tuple_args x (_tuple_args y z)" ==
    "_tuple_args x (_tuple_arg (_tuple y z))"

  "_bind (Some p) e" <= "_bind p (CONST the e)"
  "_bind (p#DUMMY) e" <= "_bind p (CONST hd e)"
  "_bind (DUMMY#p) e" <= "_bind p (CONST tl e)"

(* type constraints with spacing *)
setup {*
let
  val typ = SimpleSyntax.read_typ;
  val typeT = Syntax.typeT;
  val spropT = Syntax.spropT;
in
  Sign.del_modesyntax_i (Symbol.xsymbolsN, false) [
    ("_constrain", typ "logic => type => logic", Mixfix ("_\<Colon>_", [4, 0], 3)),
    ("_constrain", [spropT, typeT] ---> spropT, Mixfix ("_\<Colon>_", [4, 0], 3))]
  #> Sign.add_modesyntax_i (Symbol.xsymbolsN, false) [
      ("_constrain", typ "logic => type => logic", Mixfix ("_ \<Colon>  _", [4, 0], 3)),
      ("_constrain", [spropT, typeT] ---> spropT, Mixfix ("_ \<Colon> _", [4, 0], 3))]
end
*}

(* sorts as intersections *)
setup {*
let
  val sortT = Type ("sort", []); (*FIXME*)
  val classesT = Type ("classes", []); (*FIXME*)
in
  Sign.add_modesyntax_i (Symbol.xsymbolsN, false) [
    ("_topsort", sortT, Mixfix ("\<top>", [], Syntax.max_pri)),
    ("_sort", classesT --> sortT, Mixfix ("'(_')", [], Syntax.max_pri)),
    ("_classes", Lexicon.idT --> classesT --> classesT, Mixfix ("_ \<inter> _", [], Syntax.max_pri)),
    ("_classes", Lexicon.longidT --> classesT --> classesT, Mixfix ("_ \<inter> _", [], Syntax.max_pri))
  ]
end
*}

end
(*>*)
