(*  Title:      HOL/Tools/string_syntax.ML
    Author:     Makarius

Concrete syntax for characters and strings.
*)

signature STRING_SYNTAX = sig
  val hex: int -> string
  val mk_bits_syntax: int -> int -> term list
  val dest_bits_syntax: term list -> int
  val ascii_ord_of: string -> int
  val plain_strings_of: string -> string list
  datatype character = Char of string | Ord of int
  val classify_character: int -> character
end

structure String_Syntax: STRING_SYNTAX =
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


(* booleans as bits *)

fun mk_bit_syntax b =
  Syntax.const (if b = 1 then \<^const_syntax>\<open>True\<close> else \<^const_syntax>\<open>False\<close>);

fun mk_bits_syntax len = map mk_bit_syntax o Integer.radicify 2 len;

fun dest_bit_syntax (Const (\<^const_syntax>\<open>True\<close>, _)) = 1 
  | dest_bit_syntax (Const (\<^const_syntax>\<open>False\<close>, _)) = 0
  | dest_bit_syntax _ = raise Match;

val dest_bits_syntax = Integer.eval_radix 2 o map dest_bit_syntax;


(* char *)

fun ascii_ord_of c =
  if Symbol.is_ascii c then ord c
  else if c = "\<newline>" then 10
  else error ("Bad character: " ^ quote c);

fun mk_char_syntax i =
  list_comb (Syntax.const \<^const_syntax>\<open>Char\<close>, mk_bits_syntax 8 i);

fun plain_strings_of str =
  map fst (Lexicon.explode_str (str, Position.none));

datatype character = Char of string | Ord of int;

val specials = raw_explode "\\\"`'";

fun classify_character i =
  let
    val c = chr i
  in
    if not (member (op =) specials c) andalso Symbol.is_ascii c andalso Symbol.is_printable c
    then Char c
    else if c = "\n"
    then Char "\<newline>"
    else Ord i
  end;

fun dest_char_syntax b0 b1 b2 b3 b4 b5 b6 b7 =
  classify_character (dest_bits_syntax [b0, b1, b2, b3, b4, b5, b6, b7])

fun dest_char_ast (Ast.Appl [Ast.Constant \<^syntax_const>\<open>_Char\<close>, Ast.Constant s]) =
      plain_strings_of s
  | dest_char_ast _ = raise Match;

fun char_tr [(c as Const (\<^syntax_const>\<open>_constrain\<close>, _)) $ t $ u] =
      c $ char_tr [t] $ u
  | char_tr [Free (str, _)] =
      (case plain_strings_of str of
        [c] => mk_char_syntax (ascii_ord_of c)
      | _ => error ("Single character expected: " ^ str))
  | char_tr ts = raise TERM ("char_tr", ts);

fun char_ord_tr [(c as Const (\<^syntax_const>\<open>_constrain\<close>, _)) $ t $ u] =
      c $ char_ord_tr [t] $ u
  | char_ord_tr [Const (num, _)] =
      (mk_char_syntax o #value o Lexicon.read_num) num
  | char_ord_tr ts = raise TERM ("char_ord_tr", ts);

fun char_tr' [b1, b2, b3, b4, b5, b6, b7, b8] =
      (case dest_char_syntax b1 b2 b3 b4 b5 b6 b7 b8 of
        Char s => Syntax.const \<^syntax_const>\<open>_Char\<close> $
          Syntax.const (Lexicon.implode_str [s])
      | Ord n => Syntax.const \<^syntax_const>\<open>_Char_ord\<close> $
          Syntax.free (hex n))
  | char_tr' _ = raise Match;


(* string *)

fun mk_string_syntax [] = Syntax.const \<^const_syntax>\<open>Nil\<close>
  | mk_string_syntax (c :: cs) =
      Syntax.const \<^const_syntax>\<open>Cons\<close> $ mk_char_syntax (ascii_ord_of c)
        $ mk_string_syntax cs;

fun mk_string_ast ss =
  Ast.Appl [Ast.Constant \<^syntax_const>\<open>_inner_string\<close>,
    Ast.Variable (Lexicon.implode_str ss)];

fun string_tr [(c as Const (\<^syntax_const>\<open>_constrain\<close>, _)) $ t $ u] =
      c $ string_tr [t] $ u
  | string_tr [Free (str, _)] =
      mk_string_syntax (plain_strings_of str)
  | string_tr ts = raise TERM ("string_tr", ts);

fun list_ast_tr' [args] =
      Ast.Appl [Ast.Constant \<^syntax_const>\<open>_String\<close>,
        (mk_string_ast o maps dest_char_ast o Ast.unfold_ast \<^syntax_const>\<open>_args\<close>) args]
  | list_ast_tr' _ = raise Match;


(* theory setup *)

val _ =
  Theory.setup
   (Sign.parse_translation
     [(\<^syntax_const>\<open>_Char\<close>, K char_tr),
      (\<^syntax_const>\<open>_Char_ord\<close>, K char_ord_tr),
      (\<^syntax_const>\<open>_String\<close>, K string_tr)] #>
    Sign.print_translation
     [(\<^const_syntax>\<open>Char\<close>, K char_tr')] #>
    Sign.print_ast_translation
     [(\<^syntax_const>\<open>_list\<close>, K list_ast_tr')]);

end
