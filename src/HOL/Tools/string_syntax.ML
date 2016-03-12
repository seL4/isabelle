(*  Title:      HOL/Tools/string_syntax.ML
    Author:     Makarius

Concrete syntax for chars and strings.
*)

structure String_Syntax: sig end =
struct

(* numeral *)

fun hex_digit n = if n = 10 then "A"
  else if n = 11 then "B"
  else if n = 12 then "C"
  else if n = 13 then "D"
  else if n = 14 then "E"
  else if n = 15 then "F"
  else string_of_int n;

fun hex_prefix ms = "0x" ^ implode (replicate (2 - length ms) "0" @ ms);

fun hex n = hex_prefix (map hex_digit (radixpand (16, n)));


(* char *)

fun mk_char_syntax n =
  if n = 0 then Syntax.const @{const_name Groups.zero}
  else Syntax.const @{const_syntax Char} $ Numeral.mk_num_syntax n;

fun mk_char_syntax' c =
  if Symbol.is_ascii c then mk_char_syntax (ord c)
  else if c = "\<newline>" then mk_char_syntax 10
  else error ("Bad character: " ^ quote c);

fun plain_string_of str =
  map fst (Lexicon.explode_str (str, Position.none));

datatype character = Char of string | Ord of int | Unprintable;

val specials = raw_explode "\\\"`'";

fun dest_char_syntax c =
  case try Numeral.dest_num_syntax c of
    SOME n =>
      if n < 256 then
        let
          val s = chr n
        in
          if not (member (op =) specials s) andalso Symbol.is_ascii s andalso Symbol.is_printable s
          then Char s
          else if s = "\n" then Char "\<newline>"
          else Ord n
        end
      else Unprintable
  | NONE => Unprintable;

fun dest_char_ast (Ast.Appl [Ast.Constant @{syntax_const "_Char"}, Ast.Constant s]) =
      plain_string_of s
  | dest_char_ast _ = raise Match;

fun char_tr [(c as Const (@{syntax_const "_constrain"}, _)) $ t $ u] =
      c $ char_tr [t] $ u
  | char_tr [Free (str, _)] =
      (case plain_string_of str of
        [c] => mk_char_syntax' c
      | _ => error ("Single character expected: " ^ str))
  | char_tr ts = raise TERM ("char_tr", ts);

fun char_ord_tr [(c as Const (@{syntax_const "_constrain"}, _)) $ t $ u] =
      c $ char_ord_tr [t] $ u
  | char_ord_tr [Const (num, _)] =
      (mk_char_syntax o #value o Lexicon.read_num) num
  | char_ord_tr ts = raise TERM ("char_ord_tr", ts);

fun char_tr' [t] = (case dest_char_syntax t of
        Char s => Syntax.const @{syntax_const "_Char"} $
          Syntax.const (Lexicon.implode_str [s])
      | Ord n => 
          if n = 0
          then Syntax.const @{const_syntax Groups.zero}
          else Syntax.const @{syntax_const "_Char_ord"} $
            Syntax.free (hex n)
      | _ => raise Match)
  | char_tr' _ = raise Match;


(* string *)

fun mk_string_syntax [] = Syntax.const @{const_syntax Nil}
  | mk_string_syntax (c :: cs) =
      Syntax.const @{const_syntax Cons} $ mk_char_syntax' c $ mk_string_syntax cs;

fun mk_string_ast ss =
  Ast.Appl [Ast.Constant @{syntax_const "_inner_string"},
    Ast.Variable (Lexicon.implode_str ss)];

fun string_tr [(c as Const (@{syntax_const "_constrain"}, _)) $ t $ u] =
      c $ string_tr [t] $ u
  | string_tr [Free (str, _)] =
      mk_string_syntax (plain_string_of str)
  | string_tr ts = raise TERM ("char_tr", ts);

fun list_ast_tr' [args] =
      Ast.Appl [Ast.Constant @{syntax_const "_String"},
        (mk_string_ast o maps dest_char_ast o Ast.unfold_ast @{syntax_const "_args"}) args]
  | list_ast_tr' _ = raise Match;


(* theory setup *)

val _ =
  Theory.setup
   (Sign.parse_translation
     [(@{syntax_const "_Char"}, K char_tr),
      (@{syntax_const "_Char_ord"}, K char_ord_tr),
      (@{syntax_const "_String"}, K string_tr)] #>
    Sign.print_translation
     [(@{const_syntax Char}, K char_tr')] #>
    Sign.print_ast_translation
     [(@{syntax_const "_list"}, K list_ast_tr')]);

end;
