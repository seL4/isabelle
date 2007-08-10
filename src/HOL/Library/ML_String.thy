(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Monolithic strings for ML *}

theory ML_String
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
  are serialized as monolithic ML strings.
*}


subsection {* Datatype of monolithic strings *}

datatype ml_string = STR string

lemmas [code func del] = ml_string.recs ml_string.cases

lemma [code func]: "size (s\<Colon>ml_string) = 0"
  by (cases s) simp_all

subsection {* ML interface *}

ML {*
structure ML_String =
struct

fun mk s = @{term STR} $ HOLogic.mk_string s;

end;
*}


subsection {* Code serialization *}

code_type ml_string
  (SML "string")

setup {*
let
  val charr = @{const_name Char}
  val nibbles = [@{const_name Nibble0}, @{const_name Nibble1},
    @{const_name Nibble2}, @{const_name Nibble3},
    @{const_name Nibble4}, @{const_name Nibble5},
    @{const_name Nibble6}, @{const_name Nibble7},
    @{const_name Nibble8}, @{const_name Nibble9},
    @{const_name NibbleA}, @{const_name NibbleB},
    @{const_name NibbleC}, @{const_name NibbleD},
    @{const_name NibbleE}, @{const_name NibbleF}];
in
  CodeTarget.add_pretty_ml_string "SML"
    charr nibbles @{const_name Nil} @{const_name Cons} @{const_name STR}
end
*}

code_reserved SML string

code_const "op = \<Colon> ml_string \<Rightarrow> ml_string \<Rightarrow> bool"
  (SML "!((_ : string) = _)")

end
