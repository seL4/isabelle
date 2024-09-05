(*  Title:      Pure/Tools/prismjs.ML
    Author:     Makarius

Support for the Prism.js syntax highlighter -- via Isabelle/Scala.
*)

signature PRISMJS =
sig
  type language
  val languages: unit -> language list
  val language_names: language -> string list
  val language_name: language -> string
  val language_alias: language -> string list
  val check_language: Proof.context -> string * Position.T -> string
  datatype token = Token of string list * content
  and content = Atom of string | Nested of token list
  val decode_token: token XML.Decode.T
  val decode_content: content XML.Decode.T
  val token_types: token -> string list
  val token_content: token -> content
  val token_string: token -> string
  val content_string: content -> string
  val tokenize: {text: string, language: string} -> token list
end;

structure Prismjs: PRISMJS =
struct

(* languages *)

abstype language = Language of string list
with

fun language_names (Language names) = names;
val language_name = hd o language_names;
val language_alias = tl o language_names;

fun languages () =
  \<^scala>\<open>Prismjs.languages\<close> []
  |> map (split_lines #> Language);

fun check_language ctxt arg =
  let
    val langs = languages () |> maps language_names |> sort_strings |> map (rpair ());
    val name =
      Completion.check_item Markup.prismjs_languageN
        (fn (name, _) => Markup.entity Markup.prismjs_languageN name)
        langs ctxt arg;
  in name end;

end;

val _ = ML_system_pp (fn _ => fn _ => ML_Pretty.str o quote o language_name);


(* tokenize *)

datatype token = Token of string list * content
and content = Atom of string | Nested of token list;

local open XML.Decode in

fun decode_token body = body |> pair (list string) decode_content |> Token
and decode_content body =
  body |> variant
   [fn ([a], []) => Atom a,
    fn ([], a) => Nested (list decode_token a)]

end;

fun token_types (Token (types, _)) = types;
fun token_content (Token (_, content)) = content;
fun token_string tok = content_string (token_content tok)
and content_string (Atom string) = string
  | content_string (Nested tokens) = implode (map token_string tokens);

fun tokenize {text, language} =
  \<^scala>\<open>Prismjs.tokenize\<close> [text, language]
  |> map (YXML.parse_body #> decode_token);

end;
