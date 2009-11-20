(*  Title:      Tools/WWW_Find/mime.ML
    Author:     Timothy Bourke, NICTA

Rudimentary support for mime_types.
*)

signature MIME =
sig
  datatype t = Type of {
      main : string,
      sub : string, 
      params : (string * string) list
    }

  val plain : t
  val html : t
  
  val parse_type : string -> t option
  val show_type : t -> string
end;

structure Mime: MIME =
struct

datatype t = Type of {
    main : string,
    sub : string, 
    params : (string * string) list
  };

val strip =
  Substring.dropl Char.isSpace
  #> Substring.dropr Char.isSpace;

val split_fields =
  Substring.splitl (fn c => c <> #"=")
  #> apsnd (Substring.triml 1)
  #> pairself (Substring.string o strip);

fun show_param (n, v) = concat ["; ", n, "=", v];

fun show_type (Type {main, sub, params}) =
      concat ([main, "/", sub] @ map show_param params);

fun parse_type s =
  (case Substring.fields (Char.contains "/;") (Substring.full s) of
     t::s::ps => SOME (Type { main = (Substring.string o strip) t,
                              sub = (Substring.string o strip) s,
                              params = map split_fields ps })
   | _ => NONE);

val plain = the (parse_type "text/plain; charset=utf-8");
val html = the (parse_type "text/html; charset=utf-8");

end;

