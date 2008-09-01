(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Monolithic strings (message strings) for code generation *}

theory Code_Message
imports Plain "~~/src/HOL/List"
begin

subsection {* Datatype of messages *}

datatype message_string = STR string

lemmas [code func del] = message_string.recs message_string.cases

lemma [code func]: "size (s\<Colon>message_string) = 0"
  by (cases s) simp_all

lemma [code func]: "message_string_size (s\<Colon>message_string) = 0"
  by (cases s) simp_all

subsection {* ML interface *}

ML {*
structure Message_String =
struct

fun mk s = @{term STR} $ HOLogic.mk_string s;

end;
*}


subsection {* Code serialization *}

code_type message_string
  (SML "string")
  (OCaml "string")
  (Haskell "String")

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
  fold (fn target => Code_Target.add_literal_message target
    charr nibbles @{const_name Nil} @{const_name Cons} @{const_name STR})
  ["SML", "OCaml", "Haskell"]
end
*}

code_reserved SML string
code_reserved OCaml string

code_instance message_string :: eq
  (Haskell -)

code_const "op = \<Colon> message_string \<Rightarrow> message_string \<Rightarrow> bool"
  (SML "!((_ : string) = _)")
  (OCaml "!((_ : string) = _)")
  (Haskell infixl 4 "==")

end
