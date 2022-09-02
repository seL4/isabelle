(*  Title:      Pure/System/java.ML
    Author:     Makarius

Support for Java language.
*)

signature JAVA =
sig
  val print_string: string -> string
end;

structure Java: JAVA =
struct

(* string literals *)

local

val print_str =
  fn "\b" => "\\b"
   | "\t" => "\\t"
   | "\n" => "\\n"
   | "\f" => "\\f"
   | "\r" => "\\r"
   | "\"" => "\\\""
   | "\\" => "\\\\"
   | s =>
      let val c = ord s in
        if 32 < c andalso c < 127 andalso c <> 34 andalso c <> 92 then s
        else if c < 16 then "\\u000" ^ Int.fmt StringCvt.HEX c
        else if c < 128 then "\\u00" ^ Int.fmt StringCvt.HEX c
        else error ("Cannot print non-ASCII Java/Scala string literal: " ^ quote s)
      end;

in

fun print_string str =
  quote (translate_string print_str str)
    handle Fail _ => error ("Cannot print non-ASCII Java/Scala string literal: " ^ quote str);

end;

end;
