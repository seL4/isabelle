(*  Title:      HOL/Library/Pretty_Char.thy
    ID:         $Id$
    Author:     Florian Haftmann
*)

header {* Code generation of pretty characters (and strings) *}

theory Pretty_Char
imports List
begin

code_type char
  (SML "char")
  (OCaml "char")
  (Haskell "Char")

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
  fold (fn target => CodegenSerializer.add_pretty_char target charr nibbles)
    ["SML", "OCaml", "Haskell"]
  #> CodegenSerializer.add_pretty_list_string "Haskell"
    @{const_name Nil} @{const_name Cons} charr nibbles
end
*}

code_instance char :: eq
  (Haskell -)

code_reserved SML
  char

code_reserved OCaml
  char

code_const "op = \<Colon> char \<Rightarrow> char \<Rightarrow> bool"
  (SML "!((_ : char) = _)")
  (OCaml "!((_ : char) = _)")
  (Haskell infixl 4 "==")

end
