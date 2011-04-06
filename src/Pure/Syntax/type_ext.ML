(*  Title:      Pure/Syntax/type_ext.ML
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Utilities for input and output of types.  The concrete syntax of types.
*)

signature TYPE_EXT0 =
sig
  val decode_position_term: term -> Position.T option
  val is_position: term -> bool
  val strip_positions: term -> term
  val strip_positions_ast: Ast.ast -> Ast.ast
end;

signature TYPE_EXT =
sig
  include TYPE_EXT0
end;

structure Type_Ext: TYPE_EXT =
struct

(** input utils **)

(* positions *)

fun decode_position_term (Free (x, _)) = Lexicon.decode_position x
  | decode_position_term _ = NONE;

val is_position = is_some o decode_position_term;

fun strip_positions ((t as Const (c, _)) $ u $ v) =
      if (c = "_constrain" orelse c = "_constrainAbs") andalso is_position v
      then strip_positions u
      else t $ strip_positions u $ strip_positions v
  | strip_positions (t $ u) = strip_positions t $ strip_positions u
  | strip_positions (Abs (x, T, t)) = Abs (x, T, strip_positions t)
  | strip_positions t = t;

fun strip_positions_ast (Ast.Appl ((t as Ast.Constant c) :: u :: (v as Ast.Variable x) :: asts)) =
      if (c = "_constrain" orelse c = "_constrainAbs") andalso is_some (Lexicon.decode_position x)
      then Ast.mk_appl (strip_positions_ast u) (map strip_positions_ast asts)
      else Ast.Appl (map strip_positions_ast (t :: u :: v :: asts))
  | strip_positions_ast (Ast.Appl asts) = Ast.Appl (map strip_positions_ast asts)
  | strip_positions_ast ast = ast;

end;
