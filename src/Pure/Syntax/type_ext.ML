(*  Title:      Pure/Syntax/type_ext
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

The concrete syntax of types (used to bootstrap Pure)
*)

signature TYPE_EXT0 =
sig
  val typ_of_term: (indexname -> sort) -> term -> typ
end;

signature TYPE_EXT =
sig
  include TYPE_EXT0
  structure Extension: EXTENSION
  local open Extension Extension.XGram.Ast in
    val term_of_typ: bool -> typ -> term
    val tappl_ast_tr': ast * ast list -> ast
    val type_ext: ext
  end
end;

functor TypeExtFun(structure Extension: EXTENSION and Lexicon: LEXICON): TYPE_EXT =
struct

structure Extension = Extension;
open Extension Extension.XGram.Ast;


(** typ_of_term **)   (* FIXME check *)

fun typ_of_term def_sort t =
  let
    fun sort_err (xi as (x, i)) =
      error ("typ_of_term: inconsistent sort constraints for type variable " ^
        (if i < 0 then x else Lexicon.string_of_vname xi));

    fun is_tfree name =
      (case explode name of
        "'" :: _ :: _ => true
      | _ :: _ => false
      | _ => error ("typ_of_term: bad var name " ^ quote name));

    fun put_sort scs xi s =
      (case assoc (scs, xi) of
        None => (xi, s) :: scs
      | Some s' =>  if s = s' then scs else sort_err xi);

    fun classes (Const (s, _)) = [s]
      | classes (Free (s, _)) = [s]
      | classes (Const ("_sortcons", _) $ Const (s, _) $ cls) = s :: classes cls
      | classes (Const ("_sortcons", _) $ Free (s, _) $ cls) = s :: classes cls
      | classes tm = raise (TERM ("typ_of_term: bad encoding of classes", [tm]));

    fun sort (Const ("_emptysort", _)) = []
      | sort (Const (s, _)) = [s]
      | sort (Free (s, _)) = [s]
      | sort (Const ("_classes", _) $ cls) = classes cls
      | sort tm = raise (TERM ("typ_of_term: bad encoding of sort", [tm]));

    fun typ (Free (x, _), scs) =
          (if is_tfree x then TFree (x, []) else Type (x, []), scs)
      | typ (Var (xi, _), scs) = (TVar (xi, []), scs)
      | typ (Const ("_ofsort", _) $ Free (x, _) $ st, scs) =
          (TFree (x, []), put_sort scs (x, ~1) (sort st))
      | typ (Const ("_ofsort", _) $ Var (xi, _) $ st, scs) =
          (TVar (xi, []), put_sort scs xi (sort st))
      | typ (Const (a, _), scs) = (Type (a, []), scs)
      | typ (tm as (_ $ _), scs) =
          let
            val (t, ts) = strip_comb tm;
            val a =
              case t of
                Const (x, _) => x
              | Free (x, _) => x
              | _ => raise (TERM ("typ_of_term: bad type application", [tm]));
            val (tys, scs') = typs (ts, scs);
          in
            (Type (a, tys), scs')
          end
      | typ (tm, _) = raise (TERM ("typ_of_term: bad encoding of typ", [tm]))
    and typs (t :: ts, scs) =
          let
            val (ty, scs') = typ (t, scs);
            val (tys, scs'') = typs (ts, scs');
          in (ty :: tys, scs'') end
      | typs ([], scs) = ([], scs);


    val (ty, scs) = typ (t, []);

    fun get_sort xi =
      (case assoc (scs, xi) of
        None => def_sort xi
      | Some s => s);

    fun add_sorts (Type (a, tys)) = Type (a, map add_sorts tys)
      | add_sorts (TVar (xi, _)) = TVar (xi, get_sort xi)
      | add_sorts (TFree (x, _)) = TFree (x, get_sort (x, ~1));
  in
    add_sorts ty
  end;



(** term_of_typ **)

fun term_of_typ show_sorts ty =
  let
    fun const x = Const (x, dummyT);

    fun classes [] = raise Match
      | classes [s] = const s
      | classes (s :: ss) = const "_sortcons" $ const s $ classes ss;

    fun sort [] = const "_emptysort"
      | sort [s] = const s
      | sort ss = const "_classes" $ classes ss;

    fun of_sort t ss =
      if show_sorts then const "_ofsort" $ t $ sort ss else t;

    fun typ (Type (a, tys)) = list_comb (const a, map typ tys)
      | typ (TFree (x, ss)) = of_sort (Free (x, dummyT)) ss
      | typ (TVar (xi, ss)) = of_sort (Var (xi, dummyT)) ss;
  in
    typ ty
  end;



(** the type syntax **)

(* parse translations *)

fun tappl_ast_tr (*"_tappl"*) [types, f] = Appl (f :: unfold_ast "_types" types)
  | tappl_ast_tr (*"_tappl"*) asts = raise_ast "tappl_ast_tr" asts;

fun bracket_ast_tr (*"_bracket"*) [dom, cod] =
      fold_ast_p "fun" (unfold_ast "_types" dom, cod)
  | bracket_ast_tr (*"_bracket"*) asts = raise_ast "bracket_ast_tr" asts;


(* print translations *)

fun tappl_ast_tr' (f, []) = raise_ast "tappl_ast_tr'" [f]
  | tappl_ast_tr' (f, [ty]) = Appl [Constant "_tapp", ty, f]
  | tappl_ast_tr' (f, tys) = Appl [Constant "_tappl", fold_ast "_types" tys, f];

fun fun_ast_tr' (*"fun"*) asts =
  (case unfold_ast_p "fun" (Appl (Constant "fun" :: asts)) of
    (dom as (_ :: _ :: _), cod)
      => Appl [Constant "_bracket", fold_ast "_types" dom, cod]
  | _ => raise Match);


(* type_ext *)

val sortT = Type ("sort", []);
val classesT = Type ("classes", []);
val typesT = Type ("types", []);

val type_ext =
  Ext {
    roots = [logic, "type"],
    mfix = [
      Mfix ("_",           idT --> sortT,                 "", [], max_pri),
      Mfix ("{}",          sortT,                         "_emptysort", [], max_pri),
      Mfix ("{_}",         classesT --> sortT,            "_classes", [], max_pri),
      Mfix ("_",           idT --> classesT,              "", [], max_pri),
      Mfix ("_,_",         [idT, classesT] ---> classesT, "_sortcons", [], max_pri),
      Mfix ("_",           tfreeT --> typeT,              "", [], max_pri),
      Mfix ("_",           tvarT --> typeT,               "", [], max_pri),
      Mfix ("_",           idT --> typeT,                 "", [], max_pri),
      Mfix ("_::_",        [tfreeT, sortT] ---> typeT,    "_ofsort", [max_pri, 0], max_pri),
      Mfix ("_::_",        [tvarT, sortT] ---> typeT,     "_ofsort", [max_pri, 0], max_pri),
      Mfix ("_ _",         [typeT, idT] ---> typeT,       "_tapp", [max_pri, 0], max_pri),
      Mfix ("((1'(_'))_)", [typesT, idT] ---> typeT,      "_tappl", [], max_pri),
      Mfix ("_",           typeT --> typesT,              "", [], max_pri),
      Mfix ("_,/ _",       [typeT, typesT] ---> typesT,   "_types", [], max_pri),
      Mfix ("(_/ => _)",   [typeT, typeT] ---> typeT,     "fun", [1, 0], 0),
      Mfix ("([_]/ => _)", [typesT, typeT] ---> typeT,    "_bracket", [0, 0], 0)],
    extra_consts = ["fun"],
    parse_ast_translation = [("_tapp", tappl_ast_tr), ("_tappl", tappl_ast_tr),
      ("_bracket", bracket_ast_tr)],
    parse_preproc = None,
    parse_postproc = None,
    parse_translation = [],
    print_translation = [],
    print_preproc = None,
    print_postproc = None,
    print_ast_translation = [("fun", fun_ast_tr')]};


end;

