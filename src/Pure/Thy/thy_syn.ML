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

functor ThySynFun (Data: THY_SYN_DATA): THY_SYN =
struct

val syntax =
  ThyParse.make_syntax (ThyParse.pure_keywords @ Data.user_keywords)
		       (ThyParse.pure_sections @ Data.user_sections);

val parse = ThyParse.parse_thy syntax;

end;

