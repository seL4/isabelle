(*  Title:      Pure/Syntax/type_ext.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

The concrete syntax of types (used to bootstrap Pure).
*)

signature TYPE_EXT0 =
sig
  val raw_term_sorts: term -> (indexname * sort) list
  val typ_of_term: (indexname * sort) list -> (indexname -> sort) -> term -> typ
end;

signature TYPE_EXT =
sig
  include TYPE_EXT0
  structure SynExt: SYN_EXT
  local open SynExt SynExt.Ast in
    val term_of_typ: bool -> typ -> term
    val tappl_ast_tr': ast * ast list -> ast
    val type_ext: syn_ext
  end
end;

functor TypeExtFun(structure Lexicon: LEXICON and SynExt: SYN_EXT): TYPE_EXT =
struct

structure SynExt = SynExt;
open Lexicon SynExt SynExt.Ast;


(** raw_term_sorts **)

fun raw_term_sorts tm =
  let
    fun show_var (xi as (x, i)) = if i < 0 then x else string_of_vname xi;

    fun classes (Const (c, _)) = [c]
      | classes (Free (c, _)) = [c]
      | classes (Const ("_classes", _) $ Const (c, _) $ cls) = c :: classes cls
      | classes (Const ("_classes", _) $ Free (c, _) $ cls) = c :: classes cls
      | classes tm = raise_term "raw_term_sorts: bad encoding of classes" [tm];

    fun sort (Const ("_emptysort", _)) = []
      | sort (Const (s, _)) = [s]
      | sort (Free (s, _)) = [s]
      | sort (Const ("_sort", _) $ cls) = classes cls
      | sort tm = raise_term "raw_term_sorts: bad encoding of sort" [tm];

    fun env_of (Const ("_ofsort", _) $ Free (x, _) $ srt) = [((x, ~1), sort srt)]
      | env_of (Const ("_ofsort", _) $ Var (xi, _) $ srt) = [(xi, sort srt)]
      | env_of (Abs (_, _, t)) = env_of t
      | env_of (t1 $ t2) = env_of t1 @ env_of t2
      | env_of t = [];

    val env = distinct (env_of tm);
  in
    (case gen_duplicates eq_fst env of
      [] => env
    | dups => error ("Inconsistent sort constraints for type variable(s) " ^
        commas (map (quote o show_var o #1) dups)))
  end;



(** typ_of_term **)

fun typ_of_term sort_env def_sort t =
  let
    fun get_sort xi =
      (case assoc (sort_env, xi) of
        None => def_sort xi
      | Some s => s);

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
              | _ => raise_term "typ_of_term: bad encoding of type" [tm]);
          in
            Type (a, map typ_of ts)
          end;
  in
    typ_of t
  end;



(** term_of_typ **)

fun term_of_typ show_sorts ty =
  let
    fun classes [] = raise Match
      | classes [c] = free c
      | classes (c :: cs) = const "_classes" $ free c $ classes cs;

    fun sort [] = const "_emptysort"
      | sort [s] = free s
      | sort ss = const "_sort" $ classes ss;

    fun of_sort t ss =
      if show_sorts then const "_ofsort" $ t $ sort ss else t;

    fun term_of (Type (a, tys)) = list_comb (const a, map term_of tys)
      | term_of (TFree (x, ss)) = of_sort (free x) ss
      | term_of (TVar (xi, ss)) = of_sort (var xi) ss;
  in
    term_of ty
  end;



(** the type syntax **)

(* parse ast translations *)

fun tapp_ast_tr (*"_tapp"*) [ty, f] = Appl [f, ty]
  | tapp_ast_tr (*"_tapp"*) asts = raise_ast "tapp_ast_tr" asts;

fun tappl_ast_tr (*"_tappl"*) [ty, tys, f] =
      Appl (f :: ty :: unfold_ast "_types" tys)
  | tappl_ast_tr (*"_tappl"*) asts = raise_ast "tappl_ast_tr" asts;

fun bracket_ast_tr (*"_bracket"*) [dom, cod] =
      fold_ast_p "fun" (unfold_ast "_types" dom, cod)
  | bracket_ast_tr (*"_bracket"*) asts = raise_ast "bracket_ast_tr" asts;


(* print ast translations *)

fun tappl_ast_tr' (f, []) = raise_ast "tappl_ast_tr'" [f]
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
   Mfix ("{}",          sortT,                         "_emptysort", [], max_pri),
   Mfix ("{_}",         classesT --> sortT,            "_sort", [], max_pri),
   Mfix ("_",           idT --> classesT,              "", [], max_pri),
   Mfix ("_,_",         [idT, classesT] ---> classesT, "_classes", [], max_pri),
   Mfix ("_ _",         [typeT, idT] ---> typeT,       "_tapp", [max_pri, 0], max_pri),
   Mfix ("((1'(_,/ _'))_)", [typeT, typesT, idT] ---> typeT, "_tappl", [], max_pri),
   Mfix ("_",           typeT --> typesT,              "", [], max_pri),
   Mfix ("_,/ _",       [typeT, typesT] ---> typesT,   "_types", [], max_pri),
   Mfix ("(_/ => _)",   [typeT, typeT] ---> typeT,     "fun", [1, 0], 0),
   Mfix ("([_]/ => _)", [typesT, typeT] ---> typeT,    "_bracket", [0, 0], 0),
   Mfix ("'(_')",       typeT --> typeT,               "", [0], max_pri)]
  []
  ([("_tapp", tapp_ast_tr), ("_tappl", tappl_ast_tr), ("_bracket", bracket_ast_tr)],
   [],
   [],
   [("fun", fun_ast_tr')])
  ([], []);


end;
