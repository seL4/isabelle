(*  Title:      Pure/Syntax/type_ext.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Utilities for input and output of types. Also the concrete syntax of
types, which is used to bootstrap Pure.
*)

signature TYPE_EXT0 =
sig
  val raw_term_sorts: term -> (indexname * sort) list
  val typ_of_term: (indexname -> sort) -> term -> typ
end;

signature TYPE_EXT =
sig
  include TYPE_EXT0
  val term_of_sort: sort -> term
  val term_of_typ: bool -> typ -> term
  val tappl_ast_tr': Ast.ast * Ast.ast list -> Ast.ast
  val type_ext: SynExt.syn_ext
end;

structure TypeExt : TYPE_EXT =
struct

open Lexicon SynExt Ast;


(** input utils **)

(* raw_term_sorts *)

fun raw_term_sorts tm =
  let
    fun classes (Const (c, _)) = [c]
      | classes (Free (c, _)) = [c]
      | classes (Const ("_classes", _) $ Const (c, _) $ cs) = c :: classes cs
      | classes (Const ("_classes", _) $ Free (c, _) $ cs) = c :: classes cs
      | classes tm = raise TERM ("raw_term_sorts: bad encoding of classes", [tm]);

    fun sort (Const ("_topsort", _)) = []
      | sort (Const (c, _)) = [c]
      | sort (Free (c, _)) = [c]
      | sort (Const ("_sort", _) $ cs) = classes cs
      | sort tm = raise TERM ("raw_term_sorts: bad encoding of sort", [tm]);

    fun add_env (Const ("_ofsort", _) $ Free (x, _) $ cs) env = ((x, ~1), sort cs) ins env
      | add_env (Const ("_ofsort", _) $ Var (xi, _) $ cs) env = (xi, sort cs) ins env
      | add_env (Abs (_, _, t)) env = add_env t env
      | add_env (t1 $ t2) env = add_env t1 (add_env t2 env)
      | add_env t env = env;
  in
    add_env tm []
  end;


(* typ_of_term *)

fun typ_of_term get_sort t =
  let
    fun typ_of (Free (x, _)) =
          if is_tid x then TFree (x, get_sort (x, ~1))
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
  in
    typ_of t
  end;



(** output utils **)

(* term_of_sort *)

fun term_of_sort S =
  let
    fun class c = const "_class" $ free c;

    fun classes [] = sys_error "term_of_sort"
      | classes [c] = class c
      | classes (c :: cs) = const "_classes" $ class c $ classes cs;
  in
    (case S of
      [] => const "_topsort"
    | [c] => class c
    | cs => const "_sort" $ classes cs)
  end;


(* term_of_typ *)

fun term_of_typ show_sorts ty =
  let
    fun of_sort t S =
      if show_sorts then const "_ofsort" $ t $ term_of_sort S
      else t;

    fun term_of (Type (a, Ts)) = list_comb (const a, map term_of Ts)
      | term_of (TFree (x, S)) = of_sort (const "_tfree" $ free x) S
      | term_of (TVar (xi, S)) = of_sort (const "_tvar" $ var xi) S;
  in
    term_of ty
  end;



(** the type syntax **)

(* parse ast translations *)

fun tapp_ast_tr (*"_tapp"*) [ty, f] = Appl [f, ty]
  | tapp_ast_tr (*"_tapp"*) asts = raise AST ("tapp_ast_tr", asts);

fun tappl_ast_tr (*"_tappl"*) [ty, tys, f] =
      Appl (f :: ty :: unfold_ast "_types" tys)
  | tappl_ast_tr (*"_tappl"*) asts = raise AST ("tappl_ast_tr", asts);

fun bracket_ast_tr (*"_bracket"*) [dom, cod] =
      fold_ast_p "fun" (unfold_ast "_types" dom, cod)
  | bracket_ast_tr (*"_bracket"*) asts = raise AST ("bracket_ast_tr", asts);


(* print ast translations *)

fun tappl_ast_tr' (f, []) = raise AST ("tappl_ast_tr'", [f])
  | tappl_ast_tr' (f, [ty]) = Appl [Constant "_tapp", ty, f]
  | tappl_ast_tr' (f, ty :: tys) =
      Appl [Constant "_tappl", ty, fold_ast "_types" tys, f];

fun fun_ast_tr' (*"fun"*) asts =
  (case unfold_ast_p "fun" (Appl (Constant "fun" :: asts)) of
    (dom as _ :: _ :: _, cod)
      => Appl [Constant "_bracket", fold_ast "_types" dom, cod]
  | _ => raise Match);


(* type_ext *)

val sortT = Type ("sort", []);
val classesT = Type ("classes", []);
val typesT = Type ("types", []);

val type_ext = mk_syn_ext false []
  [Mfix ("_",           tidT --> typeT,                "", [], max_pri),
   Mfix ("_",           tvarT --> typeT,               "", [], max_pri),
   Mfix ("_",           idT --> typeT,                 "", [], max_pri),
   Mfix ("_::_",        [tidT, sortT] ---> typeT,      "_ofsort", [max_pri, 0], max_pri),
   Mfix ("_::_",        [tvarT, sortT] ---> typeT,     "_ofsort", [max_pri, 0], max_pri),
   Mfix ("_",           idT --> sortT,                 "", [], max_pri),
   Mfix ("{}",          sortT,                         "_topsort", [], max_pri),
   Mfix ("{_}",         classesT --> sortT,            "_sort", [], max_pri),
   Mfix ("_",           idT --> classesT,              "", [], max_pri),
   Mfix ("_,_",         [idT, classesT] ---> classesT, "_classes", [], max_pri),
   Mfix ("_ _",         [typeT, idT] ---> typeT,       "_tapp", [max_pri, 0], max_pri),
   Mfix ("((1'(_,/ _'))_)", [typeT, typesT, idT] ---> typeT, "_tappl", [], max_pri),
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
