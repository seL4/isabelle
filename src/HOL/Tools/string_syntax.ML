(*  Title:      HOL/Tools/string_syntax.ML
    Author:     Makarius

Concrete syntax for hex chars and strings.
*)

signature STRING_SYNTAX =
sig
  val setup: theory -> theory
end;

structure String_Syntax: STRING_SYNTAX =
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
  if Symbol.is_ascii s then
    Ast.Appl [Ast.Constant @{const_syntax Char}, mk_nib (ord s div 16), mk_nib (ord s mod 16)]
  else error ("Non-ASCII symbol: " ^ quote s);

val specials = raw_explode "\\\"`'";

fun dest_chr c1 c2 =
  let val c = chr (dest_nib c1 * 16 + dest_nib c2) in
    if not (member (op =) specials c) andalso Symbol.is_ascii c andalso Symbol.is_printable c
    then c else raise Match
  end;

fun dest_char (Ast.Appl [Ast.Constant @{const_syntax Char}, c1, c2]) = dest_chr c1 c2
  | dest_char _ = raise Match;

fun syntax_string cs =
  Ast.Appl [Ast.Constant @{syntax_const "_inner_string"},
    Ast.Variable (Lexicon.implode_xstr cs)];


fun char_ast_tr [Ast.Variable xstr] =
      (case Lexicon.explode_xstr xstr of
        [c] => mk_char c
      | _ => error ("Single character expected: " ^ xstr))
  | char_ast_tr [Ast.Appl [Ast.Constant @{syntax_const "_constrain"}, ast1, ast2]] =
      Ast.Appl [Ast.Constant @{syntax_const "_constrain"}, char_ast_tr [ast1], ast2]
  | char_ast_tr asts = raise Ast.AST ("char_ast_tr", asts);

fun char_ast_tr' [c1, c2] =
      Ast.Appl [Ast.Constant @{syntax_const "_Char"}, syntax_string [dest_chr c1 c2]]
  | char_ast_tr' _ = raise Match;


(* string *)

fun mk_string [] = Ast.Constant @{const_syntax Nil}
  | mk_string (c :: cs) =
      Ast.Appl [Ast.Constant @{const_syntax Cons}, mk_char c, mk_string cs];

fun string_ast_tr [Ast.Variable xstr] =
      (case Lexicon.explode_xstr xstr of
        [] =>
          Ast.Appl
            [Ast.Constant @{syntax_const "_constrain"},
              Ast.Constant @{const_syntax Nil}, Ast.Constant @{type_syntax string}]
      | cs => mk_string cs)
  | string_ast_tr [Ast.Appl [Ast.Constant @{syntax_const "_constrain"}, ast1, ast2]] =
      Ast.Appl [Ast.Constant @{syntax_const "_constrain"}, string_ast_tr [ast1], ast2]
  | string_ast_tr asts = raise Ast.AST ("string_tr", asts);

fun list_ast_tr' [args] =
      Ast.Appl [Ast.Constant @{syntax_const "_String"},
        syntax_string (map dest_char (Ast.unfold_ast @{syntax_const "_args"} args))]
  | list_ast_tr' ts = raise Match;


(* theory setup *)

val setup =
  Sign.add_trfuns
   ([(@{syntax_const "_Char"}, char_ast_tr), (@{syntax_const "_String"}, string_ast_tr)], [], [],
    [(@{const_syntax Char}, char_ast_tr'), (@{syntax_const "_list"}, list_ast_tr')]);

end;
