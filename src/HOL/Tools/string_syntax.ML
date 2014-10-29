(*  Title:      HOL/Tools/string_syntax.ML
    Author:     Makarius

Concrete syntax for hex chars and strings.
*)

structure String_Syntax: sig end =
struct

(* nibble *)

val mk_nib =
  Ast.Constant o Lexicon.mark_const o
    fst o Term.dest_Const o HOLogic.mk_nibble;

fun dest_nib (Ast.Constant s) =
  (case try Lexicon.unmark_const s of
    NONE => raise Match
  | SOME c => (HOLogic.dest_nibble (Const (c, HOLogic.nibbleT)) handle TERM _ => raise Match));


(* char *)

fun mk_char s =
  let
    val c =
      if Symbol.is_ascii s then ord s
      else if s = "\<newline>" then 10
      else error ("Bad character: " ^ quote s);
  in Ast.Appl [Ast.Constant @{const_syntax Char}, mk_nib (c div 16), mk_nib (c mod 16)] end;

val specials = raw_explode "\\\"`'";

fun dest_chr c1 c2 =
  let val s = chr (dest_nib c1 * 16 + dest_nib c2) in
    if not (member (op =) specials s) andalso Symbol.is_ascii s andalso Symbol.is_printable s
    then s
    else if s = "\n" then "\<newline>"
    else raise Match
  end;

fun dest_char (Ast.Appl [Ast.Constant @{const_syntax Char}, c1, c2]) = dest_chr c1 c2
  | dest_char _ = raise Match;

fun syntax_string ss =
  Ast.Appl [Ast.Constant @{syntax_const "_inner_string"},
    Ast.Variable (Lexicon.implode_str ss)];


fun char_ast_tr [Ast.Variable str] =
      (case Lexicon.explode_str (str, Position.none) of
        [(s, _)] => mk_char s
      | _ => error ("Single character expected: " ^ str))
  | char_ast_tr [Ast.Appl [Ast.Constant @{syntax_const "_constrain"}, ast1, ast2]] =
      Ast.Appl [Ast.Constant @{syntax_const "_constrain"}, char_ast_tr [ast1], ast2]
  | char_ast_tr asts = raise Ast.AST ("char_ast_tr", asts);

fun char_ast_tr' [c1, c2] =
      Ast.Appl [Ast.Constant @{syntax_const "_Char"}, syntax_string [dest_chr c1 c2]]
  | char_ast_tr' _ = raise Match;


(* string *)

fun mk_string [] = Ast.Constant @{const_syntax Nil}
  | mk_string (s :: ss) =
      Ast.Appl [Ast.Constant @{const_syntax Cons}, mk_char s, mk_string ss];

fun string_ast_tr [Ast.Variable str] =
      (case Lexicon.explode_str (str, Position.none) of
        [] =>
          Ast.Appl
            [Ast.Constant @{syntax_const "_constrain"},
              Ast.Constant @{const_syntax Nil}, Ast.Constant @{type_syntax string}]
      | ss => mk_string (map Symbol_Pos.symbol ss))
  | string_ast_tr [Ast.Appl [Ast.Constant @{syntax_const "_constrain"}, ast1, ast2]] =
      Ast.Appl [Ast.Constant @{syntax_const "_constrain"}, string_ast_tr [ast1], ast2]
  | string_ast_tr asts = raise Ast.AST ("string_tr", asts);

fun list_ast_tr' [args] =
      Ast.Appl [Ast.Constant @{syntax_const "_String"},
        syntax_string (map dest_char (Ast.unfold_ast @{syntax_const "_args"} args))]
  | list_ast_tr' _ = raise Match;


(* theory setup *)

val _ =
  Theory.setup
   (Sign.parse_ast_translation
     [(@{syntax_const "_Char"}, K char_ast_tr),
      (@{syntax_const "_String"}, K string_ast_tr)] #>
    Sign.print_ast_translation
     [(@{const_syntax Char}, K char_ast_tr'),
      (@{syntax_const "_list"}, K list_ast_tr')]);

end;
