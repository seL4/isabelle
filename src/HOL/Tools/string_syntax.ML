(*  Title:      HOL/Tools/string_syntax.ML
    ID:         $Id$
    Author:     Makarius

Concrete syntax for hex chars and strings.
*)

signature STRING_SYNTAX =
sig
  val setup: theory -> theory
end;

structure StringSyntax: STRING_SYNTAX =
struct


(* nibble *)

val mk_nib =
  Syntax.Constant o unprefix "List.nibble." o
  fst o Term.dest_Const o HOLogic.mk_nibble;

fun dest_nib (Syntax.Constant c) =
  HOLogic.dest_nibble (Const ("List.nibble." ^ c, dummyT))
    handle TERM _ => raise Match;


(* char *)

fun mk_char s =
  if Symbol.is_ascii s then
    Syntax.Appl [Syntax.Constant "Char", mk_nib (ord s div 16), mk_nib (ord s mod 16)]
  else error ("Non-ASCII symbol: " ^ quote s);

val specials = explode "\\\"`'";

fun dest_chr c1 c2 =
  let val c = chr (dest_nib c1 * 16 + dest_nib c2) in
    if not (member (op =) specials c) andalso Symbol.is_ascii c andalso Symbol.is_printable c
    then c else raise Match
  end;

fun dest_char (Syntax.Appl [Syntax.Constant "Char", c1, c2]) = dest_chr c1 c2
  | dest_char _ = raise Match;

fun syntax_xstr cs =
  Syntax.Appl [Syntax.Constant "_xstr", Syntax.Variable (Syntax.implode_xstr cs)];


fun char_ast_tr [Syntax.Variable xstr] =
    (case Syntax.explode_xstr xstr of
      [c] => mk_char c
    | _ => error ("Single character expected: " ^ xstr))
  | char_ast_tr asts = raise AST ("char_ast_tr", asts);

fun char_ast_tr' [c1, c2] = Syntax.Appl [Syntax.Constant "_Char", syntax_xstr [dest_chr c1 c2]]
  | char_ast_tr' _ = raise Match;


(* string *)

fun mk_string [] = Syntax.Constant "Nil"
  | mk_string (c :: cs) = Syntax.Appl [Syntax.Constant "Cons", mk_char c, mk_string cs];

fun string_ast_tr [Syntax.Variable xstr] =
    (case Syntax.explode_xstr xstr of
      [] => Syntax.Appl
        [Syntax.Constant Syntax.constrainC, Syntax.Constant "Nil", Syntax.Constant "string"]
    | cs => mk_string cs)
  | string_ast_tr asts = raise AST ("string_tr", asts);

fun list_ast_tr' [args] = Syntax.Appl [Syntax.Constant "_String",
        syntax_xstr (map dest_char (Syntax.unfold_ast "_args" args))]
  | list_ast_tr' ts = raise Match;


(* theory setup *)

val setup =
  Theory.add_trfuns
    ([("_Char", char_ast_tr), ("_String", string_ast_tr)], [], [],
      [("Char", char_ast_tr'), ("@list", list_ast_tr')]);

end;
