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
  val type_ext: Syn_Ext.syn_ext
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



(** the type syntax **)

fun typ c = Type (c, []);

val class_nameT = typ "class_name";
val type_nameT = typ "type_name";

val sortT = typ "sort";
val classesT = typ "classes";
val typesT = typ "types";

local open Lexicon Syn_Ext in

val type_ext = syn_ext' false (K false)
  [Mfix ("_",           tidT --> typeT,                "", [], max_pri),
   Mfix ("_",           tvarT --> typeT,               "", [], max_pri),
   Mfix ("_",           type_nameT --> typeT,          "", [], max_pri),
   Mfix ("_",           idT --> type_nameT,            "_type_name", [], max_pri),
   Mfix ("_",           longidT --> type_nameT,        "_type_name", [], max_pri),
   Mfix ("_::_",        [tidT, sortT] ---> typeT,      "_ofsort", [max_pri, 0], max_pri),
   Mfix ("_::_",        [tvarT, sortT] ---> typeT,     "_ofsort", [max_pri, 0], max_pri),
   Mfix ("'_()::_",     sortT --> typeT,               "_dummy_ofsort", [0], max_pri),
   Mfix ("_",           class_nameT --> sortT,         "", [], max_pri),
   Mfix ("_",           idT --> class_nameT,           "_class_name", [], max_pri),
   Mfix ("_",           longidT --> class_nameT,       "_class_name", [], max_pri),
   Mfix ("{}",          sortT,                         "_topsort", [], max_pri),
   Mfix ("{_}",         classesT --> sortT,            "_sort", [], max_pri),
   Mfix ("_",           class_nameT --> classesT,      "", [], max_pri),
   Mfix ("_,_",         [class_nameT, classesT] ---> classesT, "_classes", [], max_pri),
   Mfix ("_ _",         [typeT, type_nameT] ---> typeT, "_tapp", [max_pri, 0], max_pri),
   Mfix ("((1'(_,/ _')) _)", [typeT, typesT, type_nameT] ---> typeT, "_tappl", [], max_pri),
   Mfix ("_",           typeT --> typesT,              "", [], max_pri),
   Mfix ("_,/ _",       [typeT, typesT] ---> typesT,   "_types", [], max_pri),
   Mfix ("(_/ => _)",   [typeT, typeT] ---> typeT,     "\\<^type>fun", [1, 0], 0),
   Mfix ("([_]/ => _)", [typesT, typeT] ---> typeT,    "_bracket", [0, 0], 0),
   Mfix ("'(_')",       typeT --> typeT,               "", [0], max_pri),
   Mfix ("'_",          typeT,                         "\\<^type>dummy", [], max_pri)]
  ["_type_prop"]
  ([], [], [], [])
  []
  ([], []);

end;

end;
