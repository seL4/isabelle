(*  Title:      Pure/Thy/thy_syn.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Interface for user syntax.
*)

signature THY_SYN_DATA =
sig
  val user_keywords: string list
  val user_sections: (string * (ThyParse.token list -> (string * string)
    * ThyParse.token list)) list
end;

signature THY_SYN =
sig
  val parse: string -> string -> string
end;

functor ThySynFun(ThySynData: THY_SYN_DATA): THY_SYN =
struct

open ThyParse ThySynData;

val syntax =
  make_syntax (pure_keywords @ user_keywords) (pure_sections @ user_sections);

val parse = parse_thy syntax;

end;

