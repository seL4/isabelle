(*  Title:      http_util.ML
    Author:     Timothy Bourke, NICTA

Rudimentary utility functions for HTTP.
*)
signature HTTP_UTIL =
sig
  val crlf : string
  val reply_header : HttpStatus.t * Mime.t option * (string * string) list -> string
  val parse_query_string : string -> string Symtab.table
  val make_query_string : string Symtab.table -> string
end;

structure HttpUtil : HTTP_UTIL =
struct

val crlf = "\r\n";

fun make_header_field (name, value) = concat [name, ": ", value, crlf];

fun reply_header (status, content_type, extra_fields) =
  let
    val code = (Int.toString o HttpStatus.to_status_code) status;
    val reason = HttpStatus.to_reason status;
    val show_content_type = pair "Content-Type" o Mime.show_type;
  in
  concat
    (map make_header_field
      (("Status", concat [code, " ", reason])
       :: (the_list o Option.map show_content_type) content_type
       @ extra_fields)
    @ [crlf])
  end;

val split_fields = Substring.splitl (fn c => c <> #"=")
                   #> apsnd (Substring.triml 1);

fun decode_url s =
  let
    fun to_char c =
      Substring.triml 1 c
      |> Int.scan StringCvt.HEX Substring.getc
      |> the
      |> fst
      |> Char.chr
      |> String.str
      |> Substring.full
      handle Option => c;

    fun f (done, s) =
      let
        val (pre, post) = Substring.splitl (Char.notContains "+%") s;
      in
        if Substring.isEmpty post
        then (Substring.concat o rev) (pre::done)
        else
          if Substring.first post = SOME #"+"
            (* Substring.isPrefix "+" post *)(* seg fault in Poly/ML 5.1 *)
          then f (Substring.full " "::pre::done, Substring.triml 1 post)
          else let
            val (c, rest) = Substring.splitAt (post, 3)
                            handle Subscript =>
                              (Substring.full "%25", Substring.triml 1 post);
          in f (to_char c::pre::done, rest) end
      end;
  in f ([], s) end;

val parse_query_string =
  Substring.full
  #> Substring.tokens (Char.contains "&;")
  #> map split_fields
  #> map (pairself (UnicodeSymbols.utf8_to_symbols o decode_url))
  #> distinct ((op =) o pairself fst)
  #> Symtab.make;

local
fun to_entity #" " = "+"
  | to_entity c =
      if Char.isAlphaNum c orelse Char.contains ".-~_" c
      then String.str c
      else "%" ^ Int.fmt StringCvt.HEX (Char.ord c);
in
val encode_url = Substring.translate to_entity o Substring.full;
end

fun join_pairs (n, v) = encode_url n ^ "=" ^ encode_url v;

val make_query_string =
  Symtab.dest
  #> map join_pairs
  #> String.concatWith "&";

end;

