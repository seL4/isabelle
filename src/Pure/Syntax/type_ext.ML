(*  Title:      Pure/Syntax/type_ext.ML
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Utilities for input and output of types.  The concrete syntax of types.
*)

signature TYPE_EXT0 =
sig
  val sort_of_term: term -> sort
  val term_sorts: term -> (indexname * sort) list
  val typ_of_term: (indexname -> sort) -> term -> typ
  val type_constraint: typ -> term -> term
  val decode_term: (((string * int) * sort) list -> string * int -> sort) ->
    (string -> bool * string) -> (string -> string option) -> term -> term
  val term_of_typ: bool -> typ -> term
  val no_brackets: unit -> bool
  val no_type_brackets: unit -> bool
end;

signature TYPE_EXT =
sig
  include TYPE_EXT0
  val term_of_sort: sort -> term
  val tappl_ast_tr': Ast.ast * Ast.ast list -> Ast.ast
  val sortT: typ
  val type_ext:
   {read_class: theory -> string -> string,
    read_type: theory -> string -> string} -> SynExt.syn_ext
end;

structure TypeExt: TYPE_EXT =
struct

(** input utils **)

(* sort_of_term *)

fun sort_of_term tm =
  let
    fun err () = raise TERM ("sort_of_term: bad encoding of classes", [tm]);

    fun class s = Lexicon.unmark_class s handle Fail _ => err ();

    fun classes (Const (s, _)) = [class s]
      | classes (Const ("_classes", _) $ Const (s, _) $ cs) = class s :: classes cs
      | classes _ = err ();

    fun sort (Const ("_topsort", _)) = []
      | sort (Const (s, _)) = [class s]
      | sort (Const ("_sort", _) $ cs) = classes cs
      | sort _ = err ();
  in sort tm end;


(* term_sorts *)

fun term_sorts tm =
  let
    val sort_of = sort_of_term;

    fun add_env (Const ("_ofsort", _) $ Free (x, _) $ cs) =
          insert (op =) ((x, ~1), sort_of cs)
      | add_env (Const ("_ofsort", _) $ (Const ("_tfree", _) $ Free (x, _)) $ cs) =
          insert (op =) ((x, ~1), sort_of cs)
      | add_env (Const ("_ofsort", _) $ Var (xi, _) $ cs) =
          insert (op =) (xi, sort_of cs)
      | add_env (Const ("_ofsort", _) $ (Const ("_tvar", _) $ Var (xi, _)) $ cs) =
          insert (op =) (xi, sort_of cs)
      | add_env (Abs (_, _, t)) = add_env t
      | add_env (t1 $ t2) = add_env t1 #> add_env t2
      | add_env _ = I;
  in add_env tm [] end;


(* typ_of_term *)

fun typ_of_term get_sort tm =
  let
    fun err () = raise TERM ("typ_of_term: bad encoding of type", [tm]);

    fun typ_of (Free (x, _)) = TFree (x, get_sort (x, ~1))
      | typ_of (Var (xi, _)) = TVar (xi, get_sort xi)
      | typ_of (Const ("_tfree",_) $ (t as Free _)) = typ_of t
      | typ_of (Const ("_tvar",_) $ (t as Var _)) = typ_of t
      | typ_of (Const ("_ofsort", _) $ Free (x, _) $ _) = TFree (x, get_sort (x, ~1))
      | typ_of (Const ("_ofsort", _) $ (Const ("_tfree",_) $ Free (x, _)) $ _) =
          TFree (x, get_sort (x, ~1))
      | typ_of (Const ("_ofsort", _) $ Var (xi, _) $ _) = TVar (xi, get_sort xi)
      | typ_of (Const ("_ofsort", _) $ (Const ("_tvar",_) $ Var (xi, _)) $ _) =
          TVar (xi, get_sort xi)
      | typ_of (Const ("_dummy_ofsort", _) $ t) = TFree ("'_dummy_", sort_of_term t)
      | typ_of t =
          let
            val (head, args) = Term.strip_comb t;
            val a =
              (case head of
                Const (c, _) => (Lexicon.unmark_type c handle Fail _ => err ())
              | _ => err ());
          in Type (a, map typ_of args) end;
  in typ_of tm end;


(* decode_term -- transform parse tree into raw term *)

fun type_constraint T t =
  if T = dummyT then t
  else Const ("_type_constraint_", T --> T) $ t;

fun decode_term get_sort map_const map_free tm =
  let
    val sort_env = term_sorts tm;
    val decodeT = typ_of_term (get_sort sort_env);

    fun decode (Const ("_constrain", _) $ t $ typ) =
          type_constraint (decodeT typ) (decode t)
      | decode (Const ("_constrainAbs", _) $ (Abs (x, T, t)) $ typ) =
          if T = dummyT then Abs (x, decodeT typ, decode t)
          else type_constraint (decodeT typ --> dummyT) (Abs (x, T, decode t))
      | decode (Abs (x, T, t)) = Abs (x, T, decode t)
      | decode (t $ u) = decode t $ decode u
      | decode (Const (a, T)) =
          let val c =
            (case try Lexicon.unmark_const a of
              SOME c => c
            | NONE => snd (map_const a))
          in Const (c, T) end
      | decode (Free (a, T)) =
          (case (map_free a, map_const a) of
            (SOME x, _) => Free (x, T)
          | (_, (true, c)) => Const (c, T)
          | (_, (false, c)) => (if Long_Name.is_qualified c then Const else Free) (c, T))
      | decode (Var (xi, T)) = Var (xi, T)
      | decode (t as Bound _) = t;
  in decode tm end;



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
      | term_of (TFree (x, S)) = of_sort (Lexicon.const "_tfree" $ Lexicon.free x) S
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

val class_ast = Ast.Constant o Lexicon.mark_class;
val type_ast = Ast.Constant o Lexicon.mark_type;

fun class_name_tr read_class (*"_class_name"*) [Ast.Variable c] = class_ast (read_class c)
  | class_name_tr _ (*"_class_name"*) asts = raise Ast.AST ("class_name_tr", asts);

fun classes_tr read_class (*"_classes"*) [Ast.Variable c, ast] =
      Ast.mk_appl (Ast.Constant "_classes") [class_ast (read_class c), ast]
  | classes_tr _ (*"_classes"*) asts = raise Ast.AST ("classes_tr", asts);

fun type_name_tr read_type (*"_type_name"*) [Ast.Variable c] = type_ast (read_type c)
  | type_name_tr _ (*"_type_name"*) asts = raise Ast.AST ("type_name_tr", asts);

fun tapp_ast_tr read_type (*"_tapp"*) [ty, Ast.Variable c] =
      Ast.Appl [type_ast (read_type c), ty]
  | tapp_ast_tr _ (*"_tapp"*) asts = raise Ast.AST ("tapp_ast_tr", asts);

fun tappl_ast_tr read_type (*"_tappl"*) [ty, tys, Ast.Variable c] =
      Ast.Appl (type_ast (read_type c) :: ty :: Ast.unfold_ast "_types" tys)
  | tappl_ast_tr _ (*"_tappl"*) asts = raise Ast.AST ("tappl_ast_tr", asts);

fun bracket_ast_tr (*"_bracket"*) [dom, cod] =
      Ast.fold_ast_p "\\<^type>fun" (Ast.unfold_ast "_types" dom, cod)
  | bracket_ast_tr (*"_bracket"*) asts = raise Ast.AST ("bracket_ast_tr", asts);


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

val sortT = Type ("sort", []);
val classesT = Type ("classes", []);
val typesT = Type ("types", []);

local open Lexicon SynExt in

fun type_ext {read_class, read_type} = syn_ext' false (K false)
  [Mfix ("_",           tidT --> typeT,                "", [], max_pri),
   Mfix ("_",           tvarT --> typeT,               "", [], max_pri),
   Mfix ("_",           idT --> typeT,                 "_type_name", [], max_pri),
   Mfix ("_",           longidT --> typeT,             "_type_name", [], max_pri),
   Mfix ("_::_",        [tidT, sortT] ---> typeT,      "_ofsort", [max_pri, 0], max_pri),
   Mfix ("_::_",        [tvarT, sortT] ---> typeT,     "_ofsort", [max_pri, 0], max_pri),
   Mfix ("'_()::_",     sortT --> typeT,               "_dummy_ofsort", [0], max_pri),
   Mfix ("_",           idT --> sortT,                 "_class_name", [], max_pri),
   Mfix ("_",           longidT --> sortT,             "_class_name", [], max_pri),
   Mfix ("{}",          sortT,                         "_topsort", [], max_pri),
   Mfix ("{_}",         classesT --> sortT,            "_sort", [], max_pri),
   Mfix ("_",           idT --> classesT,              "_class_name", [], max_pri),
   Mfix ("_",           longidT --> classesT,          "_class_name", [], max_pri),
   Mfix ("_,_",         [idT, classesT] ---> classesT, "_classes", [], max_pri),
   Mfix ("_,_",         [longidT, classesT] ---> classesT, "_classes", [], max_pri),
   Mfix ("_ _",         [typeT, idT] ---> typeT,       "_tapp", [max_pri, 0], max_pri),
   Mfix ("_ _",         [typeT, longidT] ---> typeT,   "_tapp", [max_pri, 0], max_pri),
   Mfix ("((1'(_,/ _')) _)", [typeT, typesT, idT] ---> typeT, "_tappl", [], max_pri),
   Mfix ("((1'(_,/ _')) _)", [typeT, typesT, longidT] ---> typeT, "_tappl", [], max_pri),
   Mfix ("_",           typeT --> typesT,              "", [], max_pri),
   Mfix ("_,/ _",       [typeT, typesT] ---> typesT,   "_types", [], max_pri),
   Mfix ("(_/ => _)",   [typeT, typeT] ---> typeT,     "\\<^type>fun", [1, 0], 0),
   Mfix ("([_]/ => _)", [typesT, typeT] ---> typeT,    "_bracket", [0, 0], 0),
   Mfix ("'(_')",       typeT --> typeT,               "", [0], max_pri),
   Mfix ("'_",          typeT,                         "\\<^type>dummy", [], max_pri)]
  ["_type_prop"]
  (map SynExt.mk_trfun
   [("_class_name", class_name_tr o read_class o ProofContext.theory_of),
    ("_classes", classes_tr o read_class o ProofContext.theory_of),
    ("_type_name", type_name_tr o read_type o ProofContext.theory_of),
    ("_tapp", tapp_ast_tr o read_type o ProofContext.theory_of),
    ("_tappl", tappl_ast_tr o read_type o ProofContext.theory_of),
    ("_bracket", K bracket_ast_tr)],
   [],
   [],
   map SynExt.mk_trfun [("\\<^type>fun", K fun_ast_tr')])
  []
  ([], []);

end;

end;
