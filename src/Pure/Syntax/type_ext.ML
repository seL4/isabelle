(*  Title:      Pure/Syntax/type_ext.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Utilities for input and output of types.  Also the concrete syntax of
types, which is required to bootstrap Pure.
*)

signature TYPE_EXT0 =
sig
  val sort_of_term: term -> sort
  val raw_term_sorts: term -> (indexname * sort) list
  val typ_of_term: (indexname -> sort) -> term -> typ
  val term_of_typ: bool -> typ -> term
  val no_brackets: unit -> bool
end;

signature TYPE_EXT =
sig
  include TYPE_EXT0
  val term_of_sort: sort -> term
  val tappl_ast_tr': Ast.ast * Ast.ast list -> Ast.ast
  val sortT: typ
  val type_ext: SynExt.syn_ext
end;

structure TypeExt : TYPE_EXT =
struct


(** input utils **)

(* sort_of_term *)

fun sort_of_term tm =
  let
    fun classes (Const (c, _)) = [c]
      | classes (Free (c, _)) = [c]
      | classes (Const ("_classes", _) $ Const (c, _) $ cs) = c :: classes cs
      | classes (Const ("_classes", _) $ Free (c, _) $ cs) = c :: classes cs
      | classes tm = raise TERM ("sort_of_term: bad encoding of classes", [tm]);

    fun sort (Const ("_topsort", _)) = []
      | sort (Const (c, _)) = [c]
      | sort (Free (c, _)) = [c]
      | sort (Const ("_sort", _) $ cs) = classes cs
      | sort tm = raise TERM ("sort_of_term: bad encoding of sort", [tm]);
  in sort tm end;


(* raw_term_sorts *)

fun raw_term_sorts tm =
  let
    fun add_env (Const ("_ofsort", _) $ Free (x, _) $ cs) env = ((x, ~1), sort_of_term cs) ins env
      | add_env (Const ("_ofsort", _) $ Var (xi, _) $ cs) env = (xi, sort_of_term cs) ins env
      | add_env (Abs (_, _, t)) env = add_env t env
      | add_env (t1 $ t2) env = add_env t1 (add_env t2 env)
      | add_env t env = env;
  in add_env tm [] end;


(* typ_of_term *)

fun typ_of_term get_sort t =
  let
    fun typ_of (Free (x, _)) =
          if Lexicon.is_tid x then TFree (x, get_sort (x, ~1))
          else Type (x, [])
      | typ_of (Var (xi, _)) = TVar (xi, get_sort xi)
      | typ_of (Const ("_ofsort", _) $ Free (x, _) $ _) =
          TFree (x, get_sort (x, ~1))
      | typ_of (Const ("_ofsort", _) $ Var (xi, _) $ _) =
          TVar (xi, get_sort xi)
      | typ_of tm =
          let
            val (t, ts) = strip_comb tm;
            val a =
              (case t of
                Const (x, _) => x
              | Free (x, _) => x
              | _ => raise TERM ("typ_of_term: bad encoding of type", [tm]));
          in
            Type (a, map typ_of ts)
          end;
  in typ_of t end;



(** output utils **)

(* term_of_sort *)

fun term_of_sort S =
  let
    fun class c = Lexicon.const "_class" $ Lexicon.free c;

    fun classes [] = sys_error "term_of_sort"
      | classes [c] = class c
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

    fun term_of (Type (a, Ts)) = list_comb (Lexicon.const a, map term_of Ts)
      | term_of (TFree (x, S)) = of_sort (Lexicon.const "_tfree" $ Lexicon.free x) S
      | term_of (TVar (xi, S)) = of_sort (Lexicon.const "_tvar" $ Lexicon.var xi) S;
  in term_of ty end;



(** the type syntax **)

(* print mode *)

val bracketsN = "brackets";
val no_bracketsN = "no_brackets";

fun no_brackets () =
  Library.find_first (equal bracketsN orf equal no_bracketsN) (! print_mode) = Some no_bracketsN;


(* parse ast translations *)

fun tapp_ast_tr (*"_tapp"*) [ty, f] = Ast.Appl [f, ty]
  | tapp_ast_tr (*"_tapp"*) asts = raise Ast.AST ("tapp_ast_tr", asts);

fun tappl_ast_tr (*"_tappl"*) [ty, tys, f] =
      Ast.Appl (f :: ty :: Ast.unfold_ast "_types" tys)
  | tappl_ast_tr (*"_tappl"*) asts = raise Ast.AST ("tappl_ast_tr", asts);

fun bracket_ast_tr (*"_bracket"*) [dom, cod] =
      Ast.fold_ast_p "fun" (Ast.unfold_ast "_types" dom, cod)
  | bracket_ast_tr (*"_bracket"*) asts = raise Ast.AST ("bracket_ast_tr", asts);


(* print ast translations *)

fun tappl_ast_tr' (f, []) = raise Ast.AST ("tappl_ast_tr'", [f])
  | tappl_ast_tr' (f, [ty]) = Ast.Appl [Ast.Constant "_tapp", ty, f]
  | tappl_ast_tr' (f, ty :: tys) =
      Ast.Appl [Ast.Constant "_tappl", ty, Ast.fold_ast "_types" tys, f];

fun fun_ast_tr' (*"fun"*) asts =
  if no_brackets () then raise Match
  else
    (case Ast.unfold_ast_p "fun" (Ast.Appl (Ast.Constant "fun" :: asts)) of
      (dom as _ :: _ :: _, cod)
        => Ast.Appl [Ast.Constant "_bracket", Ast.fold_ast "_types" dom, cod]
    | _ => raise Match);


(* type_ext *)

val sortT = Type ("sort", []);
val classesT = Type ("classes", []);
val typesT = Type ("types", []);

local open Lexicon SynExt in

val type_ext = mk_syn_ext false ["dummy"]
  [Mfix ("_",           tidT --> typeT,                "", [], max_pri),
   Mfix ("_",           tvarT --> typeT,               "", [], max_pri),
   Mfix ("_",           idT --> typeT,                 "", [], max_pri),
   Mfix ("_",           longidT --> typeT,             "", [], max_pri),
   Mfix ("_::_",        [tidT, sortT] ---> typeT,      "_ofsort", [max_pri, 0], max_pri),
   Mfix ("_::_",        [tvarT, sortT] ---> typeT,     "_ofsort", [max_pri, 0], max_pri),
   Mfix ("_",           idT --> sortT,                 "", [], max_pri),
   Mfix ("_",           longidT --> sortT,             "", [], max_pri),
   Mfix ("{}",          sortT,                         "_topsort", [], max_pri),
   Mfix ("{_}",         classesT --> sortT,            "_sort", [], max_pri),
   Mfix ("_",           idT --> classesT,              "", [], max_pri),
   Mfix ("_",           longidT --> classesT,          "", [], max_pri),
   Mfix ("_,_",         [idT, classesT] ---> classesT, "_classes", [], max_pri),
   Mfix ("_,_",         [longidT, classesT] ---> classesT, "_classes", [], max_pri),
   Mfix ("_ _",         [typeT, idT] ---> typeT,       "_tapp", [max_pri, 0], max_pri),
   Mfix ("_ _",         [typeT, longidT] ---> typeT,   "_tapp", [max_pri, 0], max_pri),
   Mfix ("((1'(_,/ _')) _)", [typeT, typesT, idT] ---> typeT, "_tappl", [], max_pri),
   Mfix ("((1'(_,/ _')) _)", [typeT, typesT, longidT] ---> typeT, "_tappl", [], max_pri),
   Mfix ("_",           typeT --> typesT,              "", [], max_pri),
   Mfix ("_,/ _",       [typeT, typesT] ---> typesT,   "_types", [], max_pri),
   Mfix ("(_/ => _)",   [typeT, typeT] ---> typeT,     "fun", [1, 0], 0),
   Mfix ("([_]/ => _)", [typesT, typeT] ---> typeT,    "_bracket", [0, 0], 0),
   Mfix ("'(_')",       typeT --> typeT,               "", [0], max_pri),
   Mfix ("'_",          typeT,                         "dummy", [], max_pri)]
  []
  ([("_tapp", tapp_ast_tr), ("_tappl", tappl_ast_tr), ("_bracket", bracket_ast_tr)],
   [],
   [],
   [("fun", fun_ast_tr')])
  TokenTrans.token_translation
  ([], []);

end;

end;
