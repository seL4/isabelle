(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Monolithic strings for ML  *}

theory MLString
imports List
begin

subsection {* Motivation *}

text {*
  Strings are represented in HOL as list of characters.
  For code generation to Haskell, this is no problem
  since in Haskell "abc" is equivalent to ['a', 'b', 'c'].
  On the other hand, in ML all strings have to
  be represented as list of characters which
  is awkward to read. This theory provides a distinguished
  datatype for strings which then by convention
  are serialized as monolithic ML strings. Note
  that in Haskell these strings are identified
  with Haskell strings.
*}


subsection {* Datatype of monolithic strings *}

datatype ml_string = STR string

fun
  explode :: "ml_string \<Rightarrow> string"
where
  "explode (STR s) = s"


subsection {* ML interface *}

ML {*
structure MLString =
struct

fun mk s = @{term STR} $ HOLogic.mk_string s;

end;
*}


subsection {* Code serialization *}

code_type ml_string
  (SML "string")
  (Haskell "String")

code_const STR
  (Haskell "_")

setup {*
  CodegenSerializer.add_pretty_ml_string "SML"
    @{const_name Nil} @{const_name Cons} @{const_name STR}
    ML_Syntax.print_char ML_Syntax.print_string "String.implode"
*}

code_const explode
  (SML "String.explode")
  (Haskell "_")

code_reserved SML string explode

code_const "op = \<Colon> ml_string \<Rightarrow> ml_string \<Rightarrow> bool"
  (SML "!((_ : string) = _)")
  (Haskell infixl 4 "==")

code_instance ml_string :: eq (Haskell -)

text {* disable something ugly *}

code_const "ml_string_rec" and "ml_string_case" and "size \<Colon> ml_string \<Rightarrow> nat"
  (SML "!((_); (_); raise Fail \"ml'_string'_rec\")"
    and "!((_); (_); raise Fail \"ml'_string'_case\")"
    and "!((_); raise Fail \"size'_ml'_string\")")

end
