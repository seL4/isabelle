(*  Title:      HOL/ex/Antiquote.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Simple quote / antiquote example.
*)

Antiquote = Arith +

syntax
  "_Expr" :: "'a => 'a"				("EXPR _" [1000] 999)

constdefs
  var :: "'a => ('a => nat) => nat"		("VAR _" [1000] 999)
  "var x env == env x"

  Expr :: "'a => 'a"
	(*"(('a => nat) => nat) => (('a => nat) => nat)"*)
  "Expr == (%x. x)"

end


ML

val parse_translation = [Syntax.quote_antiquote_tr "_Expr" "var" "Expr"];
val print_translation = [Syntax.quote_antiquote_tr' "_Expr" "var" "Expr"];
