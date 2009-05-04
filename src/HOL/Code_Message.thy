(* Author: Florian Haftmann, TU Muenchen *)

header {* Monolithic strings (message strings) for code generation *}

theory Code_Message
imports Plain "~~/src/HOL/List"
begin

subsection {* Datatype of messages *}

datatype message_string = STR string

lemmas [code del] = message_string.recs message_string.cases

lemma [code]: "size (s\<Colon>message_string) = 0"
  by (cases s) simp_all

lemma [code]: "message_string_size (s\<Colon>message_string) = 0"
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
  fold (fn target => add_literal_message @{const_name STR} target)
    ["SML", "OCaml", "Haskell"]
*}

code_reserved SML string
code_reserved OCaml string

code_instance message_string :: eq
  (Haskell -)

code_const "eq_class.eq \<Colon> message_string \<Rightarrow> message_string \<Rightarrow> bool"
  (SML "!((_ : string) = _)")
  (OCaml "!((_ : string) = _)")
  (Haskell infixl 4 "==")

end
