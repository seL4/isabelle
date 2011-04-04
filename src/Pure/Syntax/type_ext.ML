(*  Title:      Pure/Syntax/type_ext.ML
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Utilities for input and output of types.  The concrete syntax of types.
*)

signature TYPE_EXT0 =
sig
  val sort_of_term: term -> sort
  val term_sorts: term -> (indexname * sort) list
  val typ_of_term: (indexname -> sort) -> term -> typ
  val is_position: term -> bool
  val strip_positions: term -> term
  val strip_positions_ast: Ast.ast -> Ast.ast
  type term_context
  val decode_term: term_context -> Position.reports * term -> Position.reports * term
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
  val type_ext: Syn_Ext.syn_ext
end;

structure Type_Ext: TYPE_EXT =
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


(* positions *)

fun decode_position (Free (x, _)) = Lexicon.decode_position x
  | decode_position _ = NONE;

val is_position = is_some o decode_position;

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


(* decode_term -- transform parse tree into raw term *)

fun markup_bound def id =
  [Markup.properties [(if def then Markup.defN else Markup.refN, id)] Markup.bound];

type term_context =
 {get_sort: (indexname * sort) list -> indexname -> sort,
  get_const: string -> bool * string,
  get_free: string -> string option,
  markup_const: string -> Markup.T list,
  markup_free: string -> Markup.T list,
  markup_var: indexname -> Markup.T list};

fun decode_term (term_context: term_context) (reports0: Position.reports, tm) =
  let
    val {get_sort, get_const, get_free, markup_const, markup_free, markup_var} = term_context;
    val decodeT = typ_of_term (get_sort (term_sorts tm));

    val reports = Unsynchronized.ref reports0;
    fun report ps = Position.reports reports ps;

    fun decode ps qs bs (Const ("_constrain", _) $ t $ typ) =
          (case decode_position typ of
            SOME p => decode (p :: ps) qs bs t
          | NONE => Type.constraint (decodeT typ) (decode ps qs bs t))
      | decode ps qs bs (Const ("_constrainAbs", _) $ t $ typ) =
          (case decode_position typ of
            SOME q => decode ps (q :: qs) bs t
          | NONE => Type.constraint (decodeT typ --> dummyT) (decode ps qs bs t))
      | decode _ qs bs (Abs (x, T, t)) =
          let
            val id = serial_string ();
            val _ = report qs (markup_bound true) id;
          in Abs (x, T, decode [] [] (id :: bs) t) end
      | decode _ _ bs (t $ u) = decode [] [] bs t $ decode [] [] bs u
      | decode ps _ _ (Const (a, T)) =
          (case try Lexicon.unmark_fixed a of
            SOME x => (report ps markup_free x; Free (x, T))
          | NONE =>
              let
                val c =
                  (case try Lexicon.unmark_const a of
                    SOME c => c
                  | NONE => snd (get_const a));
                val _ = report ps markup_const c;
              in Const (c, T) end)
      | decode ps _ _ (Free (a, T)) =
          (case (get_free a, get_const a) of
            (SOME x, _) => (report ps markup_free x; Free (x, T))
          | (_, (true, c)) => (report ps markup_const c; Const (c, T))
          | (_, (false, c)) =>
              if Long_Name.is_qualified c
              then (report ps markup_const c; Const (c, T))
              else (report ps markup_free c; Free (c, T)))
      | decode ps _ _ (Var (xi, T)) = (report ps markup_var xi; Var (xi, T))
      | decode ps _ bs (t as Bound i) =
          (case try (nth bs) i of
            SOME id => (report ps (markup_bound false) id; t)
          | NONE => t);

    val tm' = decode [] [] [] tm;
  in (! reports, tm') end;



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
