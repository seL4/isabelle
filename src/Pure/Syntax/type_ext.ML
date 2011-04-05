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
  val term_of_typ: bool -> typ -> term
  val no_brackets: unit -> bool
  val no_type_brackets: unit -> bool
end;

signature TYPE_EXT =
sig
  include TYPE_EXT0
  val term_of_sort: sort -> term
  val tappl_ast_tr': Ast.ast * Ast.ast list -> Ast.ast
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



(** output utils **)

(* term_of_sort *)

fun term_of_sort S =
  let
    val class = Lexicon.const o Lexicon.mark_class;

    fun classes [c] = class c
      | classes (c :: cs) = Lexicon.const "_classes" $ class c $ classes cs;
  in
    (case S of
      [] => Lexicon.const "_topsort"
    | [c] => class c
    | cs => Lexicon.const "_sort" $ classes cs)
  end;


(* term_of_typ *)

fun term_of_typ show_sorts ty =
  let
    fun of_sort t S =
      if show_sorts then Lexicon.const "_ofsort" $ t $ term_of_sort S
      else t;

    fun term_of (Type (a, Ts)) =
          Term.list_comb (Lexicon.const (Lexicon.mark_type a), map term_of Ts)
      | term_of (TFree (x, S)) =
          if is_some (Lexicon.decode_position x) then Lexicon.free x
          else of_sort (Lexicon.const "_tfree" $ Lexicon.free x) S
      | term_of (TVar (xi, S)) = of_sort (Lexicon.const "_tvar" $ Lexicon.var xi) S;
  in term_of ty end;



(** the type syntax **)

(* print mode *)

val bracketsN = "brackets";
val no_bracketsN = "no_brackets";

fun no_brackets () =
  find_first (fn mode => mode = bracketsN orelse mode = no_bracketsN)
    (print_mode_value ()) = SOME no_bracketsN;

val type_bracketsN = "type_brackets";
val no_type_bracketsN = "no_type_brackets";

fun no_type_brackets () =
  find_first (fn mode => mode = type_bracketsN orelse mode = no_type_bracketsN)
    (print_mode_value ()) <> SOME type_bracketsN;


(* parse ast translations *)

fun tapp_ast_tr [ty, c] = Ast.Appl [c, ty]
  | tapp_ast_tr asts = raise Ast.AST ("tapp_ast_tr", asts);

fun tappl_ast_tr [ty, tys, c] = Ast.mk_appl c (ty :: Ast.unfold_ast "_types" tys)
  | tappl_ast_tr asts = raise Ast.AST ("tappl_ast_tr", asts);

fun bracket_ast_tr [dom, cod] = Ast.fold_ast_p "\\<^type>fun" (Ast.unfold_ast "_types" dom, cod)
  | bracket_ast_tr asts = raise Ast.AST ("bracket_ast_tr", asts);


(* print ast translations *)

fun tappl_ast_tr' (f, []) = raise Ast.AST ("tappl_ast_tr'", [f])
  | tappl_ast_tr' (f, [ty]) = Ast.Appl [Ast.Constant "_tapp", ty, f]
  | tappl_ast_tr' (f, ty :: tys) =
      Ast.Appl [Ast.Constant "_tappl", ty, Ast.fold_ast "_types" tys, f];

fun fun_ast_tr' (*"\\<^type>fun"*) asts =
  if no_brackets () orelse no_type_brackets () then raise Match
  else
    (case Ast.unfold_ast_p "\\<^type>fun" (Ast.Appl (Ast.Constant "\\<^type>fun" :: asts)) of
      (dom as _ :: _ :: _, cod)
        => Ast.Appl [Ast.Constant "_bracket", Ast.fold_ast "_types" dom, cod]
    | _ => raise Match);


(* type_ext *)

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
  (map Syn_Ext.mk_trfun
    [("_tapp", K tapp_ast_tr), ("_tappl", K tappl_ast_tr), ("_bracket", K bracket_ast_tr)],
   [], [], map Syn_Ext.mk_trfun [("\\<^type>fun", K fun_ast_tr')])
  []
  ([], []);

end;

end;
