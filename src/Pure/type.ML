(*  Title:      Pure/type.ML
    ID:         $Id$
    Author:     Tobias Nipkow, Lawrence C Paulson, and Markus Wenzel

Type signatures and certified types, special treatment of type vars,
matching and unification of types, extend and merge type signatures.
*)

signature TYPE =
sig
  (*type signatures and certified types*)
  datatype decl =
    LogicalType of int |
    Abbreviation of string list * typ * bool |
    Nonterminal
  type tsig
  val rep_tsig: tsig ->
   {classes: NameSpace.T * Sorts.classes,
    default: sort,
    types: (decl * stamp) NameSpace.table,
    arities: Sorts.arities,
    log_types: string list,
    witness: (typ * sort) option}
  val empty_tsig: tsig
  val classes: tsig -> class list
  val defaultS: tsig -> sort
  val logical_types: tsig -> string list
  val universal_witness: tsig -> (typ * sort) option
  val eq_sort: tsig -> sort * sort -> bool
  val subsort: tsig -> sort * sort -> bool
  val of_sort: tsig -> typ * sort -> bool
  val inter_sort: tsig -> sort * sort -> sort
  val cert_class: tsig -> class -> class
  val cert_sort: tsig -> sort -> sort
  val witness_sorts: tsig -> sort list -> sort list -> (typ * sort) list
  val cert_typ: tsig -> typ -> typ
  val cert_typ_syntax: tsig -> typ -> typ
  val cert_typ_abbrev: tsig -> typ -> typ
  val arity_number: tsig -> string -> int
  val arity_sorts: Pretty.pp -> tsig -> string -> sort -> sort list

  (*special treatment of type vars*)
  val strip_sorts: typ -> typ
  val no_tvars: typ -> typ
  val varifyT: typ -> typ
  val unvarifyT: typ -> typ
  val varify: term * (string * sort) list -> term * ((string * sort) * indexname) list
  val freeze_thaw_type: typ -> typ * (typ -> typ)
  val freeze_type: typ -> typ
  val freeze_thaw: term -> term * (term -> term)
  val freeze: term -> term

  (*matching and unification*)
  exception TYPE_MATCH
  type tyenv
  val lookup: tyenv * (indexname * sort) -> typ option
  val typ_match: tsig -> typ * typ -> tyenv -> tyenv
  val typ_instance: tsig -> typ * typ -> bool
  val raw_match: typ * typ -> tyenv -> tyenv
  val raw_instance: typ * typ -> bool
  exception TUNIFY
  val unify: tsig -> typ * typ -> tyenv * int -> tyenv * int
  val raw_unify: typ * typ -> tyenv -> tyenv
  val could_unify: typ * typ -> bool
  val eq_type: tyenv -> typ * typ -> bool

  (*extend and merge type signatures*)
  val add_class: Pretty.pp -> NameSpace.naming -> bstring * class list -> tsig -> tsig
  val hide_classes: bool -> string list -> tsig -> tsig
  val set_defsort: sort -> tsig -> tsig
  val add_types: NameSpace.naming -> (bstring * int) list -> tsig -> tsig
  val add_abbrevs: NameSpace.naming -> (string * string list * typ) list -> tsig -> tsig
  val add_nonterminals: NameSpace.naming -> string list -> tsig -> tsig
  val hide_types: bool -> string list -> tsig -> tsig
  val add_arity: Pretty.pp -> arity -> tsig -> tsig
  val add_classrel: Pretty.pp -> class * class -> tsig -> tsig
  val merge_tsigs: Pretty.pp -> tsig * tsig -> tsig
end;

structure Type: TYPE =
struct

(** type signatures and certified types **)

(* type declarations *)

datatype decl =
  LogicalType of int |
  Abbreviation of string list * typ * bool |
  Nonterminal;

fun str_of_decl (LogicalType _) = "logical type constructor"
  | str_of_decl (Abbreviation _) = "type abbreviation"
  | str_of_decl Nonterminal = "syntactic type";


(* type tsig *)

datatype tsig =
  TSig of {
    classes: NameSpace.T * Sorts.classes,   (*declared classes with proper subclass relation*)
    default: sort,                          (*default sort on input*)
    types: (decl * stamp) NameSpace.table,  (*declared types*)
    arities: Sorts.arities,                 (*image specification of types wrt. sorts*)
    log_types: string list,                 (*logical types sorted by number of arguments*)
    witness: (typ * sort) option};          (*witness for non-emptiness of strictest sort*)

fun rep_tsig (TSig comps) = comps;

fun make_tsig (classes, default, types, arities, log_types, witness) =
  TSig {classes = classes, default = default, types = types, arities = arities,
    log_types = log_types, witness = witness};

fun build_tsig (classes, default, types, arities) =
  let
    val log_types =
      Symtab.fold (fn (c, (LogicalType n, _)) => cons (c, n) | _ => I) (snd types) []
      |> Library.sort (Library.int_ord o pairself snd) |> map fst;
    val witness =
      (case Sorts.witness_sorts (snd classes, arities) log_types [] [Graph.keys (snd classes)] of
        [w] => SOME w | _ => NONE);
  in make_tsig (classes, default, types, arities, log_types, witness) end;

fun map_tsig f (TSig {classes, default, types, arities, log_types = _, witness = _}) =
  build_tsig (f (classes, default, types, arities));

val empty_tsig =
  build_tsig ((NameSpace.empty, Graph.empty), [], NameSpace.empty_table, Symtab.empty);


(* classes and sorts *)

fun classes (TSig {classes = (_, C), ...}) = Graph.keys C;
fun defaultS (TSig {default, ...}) = default;
fun logical_types (TSig {log_types, ...}) = log_types;
fun universal_witness (TSig {witness, ...}) = witness;

fun eq_sort (TSig {classes, ...}) = Sorts.sort_eq (#2 classes);
fun subsort (TSig {classes, ...}) = Sorts.sort_le (#2 classes);
fun of_sort (TSig {classes, arities, ...}) = Sorts.of_sort (#2 classes, arities);
fun inter_sort (TSig {classes, ...}) = Sorts.inter_sort (#2 classes);

fun cert_class (TSig {classes, ...}) c =
  if can (Graph.get_node (#2 classes)) c then c
  else raise TYPE ("Undeclared class: " ^ quote c, [], []);

fun cert_sort (tsig as TSig {classes, ...}) =
  Sorts.norm_sort (#2 classes) o map (cert_class tsig);

fun witness_sorts (tsig as TSig {classes, arities, log_types, ...}) =
  Sorts.witness_sorts (#2 classes, arities) log_types;


(* certified types *)

fun bad_nargs t = "Bad number of arguments for type constructor: " ^ quote t;
fun undecl_type c = "Undeclared type constructor: " ^ quote c;

local

fun inst_typ env (Type (c, Ts)) = Type (c, map (inst_typ env) Ts)
  | inst_typ env (T as TFree (x, _)) = the_default T (AList.lookup (op =) env x)
  | inst_typ _ T = T;

fun certify_typ normalize syntax tsig ty =
  let
    val TSig {types = (_, types), ...} = tsig;
    fun err msg = raise TYPE (msg, [ty], []);

    val check_syntax =
      if syntax then K ()
      else fn c => err ("Illegal occurrence of syntactic type: " ^ quote c);

    fun cert (T as Type (c, Ts)) =
          let
            val Ts' = map cert Ts;
            fun nargs n = if length Ts <> n then err (bad_nargs c) else ();
          in
            (case Symtab.lookup types c of
              SOME (LogicalType n, _) => (nargs n; Type (c, Ts'))
            | SOME (Abbreviation (vs, U, syn), _) => (nargs (length vs);
                if syn then check_syntax c else ();
                if normalize then inst_typ (vs ~~ Ts') U
                else Type (c, Ts'))
            | SOME (Nonterminal, _) => (nargs 0; check_syntax c; T)
            | NONE => err (undecl_type c))
          end
      | cert (TFree (x, S)) = TFree (x, cert_sort tsig S)
      | cert (TVar (xi as (_, i), S)) =
          if i < 0 then
            err ("Malformed type variable: " ^ quote (Term.string_of_vname xi))
          else TVar (xi, cert_sort tsig S);

    val ty' = cert ty;
  in if ty = ty' then ty else ty' end;  (*avoid copying of already normal type*)

in

val cert_typ        = certify_typ true false;
val cert_typ_syntax = certify_typ true true;
val cert_typ_abbrev = certify_typ false true;

end;


(* type arities *)

fun arity_number (TSig {types = (_, types), ...}) a =
  (case Symtab.lookup types a of
    SOME (LogicalType n, _) => n
  | _ => error (undecl_type a));

fun arity_sorts _ tsig a [] = replicate (arity_number tsig a) []
  | arity_sorts pp (TSig {classes, arities, ...}) a S =
      Sorts.mg_domain (#2 classes, arities) a S handle Sorts.DOMAIN (a, c) =>
        error ("No way to get " ^ Pretty.string_of_arity pp (a, [], [c]));



(** special treatment of type vars **)

(* strip_sorts *)

fun strip_sorts (Type (a, Ts)) = Type (a, map strip_sorts Ts)
  | strip_sorts (TFree (x, _)) = TFree (x, [])
  | strip_sorts (TVar (xi, _)) = TVar (xi, []);


(* no_tvars *)

fun no_tvars T =
  (case typ_tvars T of [] => T
  | vs => raise TYPE ("Illegal schematic type variable(s): " ^
      commas_quote (map (Term.string_of_vname o #1) vs), [T], []));


(* varify, unvarify *)

val varifyT = map_type_tfree (fn (a, S) => TVar ((a, 0), S));
val unvarifyT = map_type_tvar (fn ((a, 0), S) => TFree (a, S) | v => TVar v);

fun varify (t, fixed) =
  let
    val fs = Term.fold_types (Term.fold_atyps
      (fn TFree v => if member (op =) fixed v then I else insert (op =) v | _ => I)) t [];
    val ixns = add_term_tvar_ixns (t, []);
    val fmap = fs ~~ map (rpair 0) (variantlist (map fst fs, map #1 ixns))
    fun thaw (f as (a, S)) =
      (case AList.lookup (op =) fmap f of
        NONE => TFree f
      | SOME xi => TVar (xi, S));
  in (map_term_types (map_type_tfree thaw) t, fmap) end;


(* freeze_thaw: freeze TVars in a term; return the "thaw" inverse *)

local

fun new_name (ix, (pairs, used)) =
  let val v = variant used (string_of_indexname ix)
  in ((ix, v) :: pairs, v :: used) end;

fun freeze_one alist (ix, sort) =
  TFree (the (AList.lookup (op =) alist ix), sort)
    handle Option =>
      raise TYPE ("Failure during freezing of ?" ^ string_of_indexname ix, [], []);

fun thaw_one alist (a, sort) = TVar (the (AList.lookup (op =) alist a), sort)
  handle Option => TFree (a, sort);

in

(*this sort of code could replace unvarifyT*)
fun freeze_thaw_type T =
  let
    val used = add_typ_tfree_names (T, [])
    and tvars = map #1 (add_typ_tvars (T, []));
    val (alist, _) = foldr new_name ([], used) tvars;
  in (map_type_tvar (freeze_one alist) T, map_type_tfree (thaw_one (map swap alist))) end;

val freeze_type = #1 o freeze_thaw_type;

fun freeze_thaw t =
  let
    val used = it_term_types add_typ_tfree_names (t, [])
    and tvars = map #1 (it_term_types add_typ_tvars (t, []));
    val (alist, _) = foldr new_name ([], used) tvars;
  in
    (case alist of
      [] => (t, fn x => x) (*nothing to do!*)
    | _ => (map_term_types (map_type_tvar (freeze_one alist)) t,
      map_term_types (map_type_tfree (thaw_one (map swap alist)))))
  end;

val freeze = #1 o freeze_thaw;

end;



(** matching and unification of types **)

type tyenv = (sort * typ) Vartab.table;

fun tvar_clash ixn S S' = raise TYPE ("Type variable " ^
  quote (Term.string_of_vname ixn) ^ " has two distinct sorts",
  [TVar (ixn, S), TVar (ixn, S')], []);

fun lookup (tye, (ixn, S)) =
  (case Vartab.lookup tye ixn of
    NONE => NONE
  | SOME (S', T) => if S = S' then SOME T else tvar_clash ixn S S');


(* matching *)

exception TYPE_MATCH;

fun typ_match tsig =
  let
    fun match (TVar (v, S), T) subs =
          (case lookup (subs, (v, S)) of
            NONE =>
              if of_sort tsig (T, S) then Vartab.update_new (v, (S, T)) subs
              else raise TYPE_MATCH
          | SOME U => if U = T then subs else raise TYPE_MATCH)
      | match (Type (a, Ts), Type (b, Us)) subs =
          if a <> b then raise TYPE_MATCH
          else matches (Ts, Us) subs
      | match (TFree x, TFree y) subs =
          if x = y then subs else raise TYPE_MATCH
      | match _ _ = raise TYPE_MATCH
    and matches (T :: Ts, U :: Us) subs = matches (Ts, Us) (match (T, U) subs)
      | matches _ subs = subs;
  in match end;

fun typ_instance tsig (T, U) =
  (typ_match tsig (U, T) Vartab.empty; true) handle TYPE_MATCH => false;

(*purely structural matching*)
fun raw_match (TVar (v, S), T) subs =
      (case lookup (subs, (v, S)) of
        NONE => Vartab.update_new (v, (S, T)) subs
      | SOME U => if U = T then subs else raise TYPE_MATCH)
  | raw_match (Type (a, Ts), Type (b, Us)) subs =
      if a <> b then raise TYPE_MATCH
      else raw_matches (Ts, Us) subs
  | raw_match (TFree x, TFree y) subs =
      if x = y then subs else raise TYPE_MATCH
  | raw_match _ _ = raise TYPE_MATCH
and raw_matches (T :: Ts, U :: Us) subs = raw_matches (Ts, Us) (raw_match (T, U) subs)
  | raw_matches _ subs = subs;

fun raw_instance (T, U) =
  (raw_match (U, T) Vartab.empty; true) handle TYPE_MATCH => false;


(* unification *)

exception TUNIFY;

(*occurs_check*)
fun occurs v tye =
  let
    fun occ (Type (_, Ts)) = exists occ Ts
      | occ (TFree _) = false
      | occ (TVar (w, S)) =
          eq_ix (v, w) orelse
            (case lookup (tye, (w, S)) of
              NONE => false
            | SOME U => occ U);
  in occ end;

(*chase variable assignments; if devar returns a type var then it must be unassigned*)
fun devar tye (T as TVar v) =
      (case lookup (tye, v) of
        SOME U => devar tye U
      | NONE => T)
  | devar tye T = T;

(*order-sorted unification*)
fun unify (tsig as TSig {classes = (_, classes), arities, ...}) TU (tyenv, maxidx) =
  let
    val tyvar_count = ref maxidx;
    fun gen_tyvar S = TVar (("'a", inc tyvar_count), S);

    fun mg_domain a S =
      Sorts.mg_domain (classes, arities) a S handle Sorts.DOMAIN _ => raise TUNIFY;

    fun meet (_, []) tye = tye
      | meet (TVar (xi, S'), S) tye =
          if Sorts.sort_le classes (S', S) then tye
          else Vartab.update_new
            (xi, (S', gen_tyvar (Sorts.inter_sort classes (S', S)))) tye
      | meet (TFree (_, S'), S) tye =
          if Sorts.sort_le classes (S', S) then tye
          else raise TUNIFY
      | meet (Type (a, Ts), S) tye = meets (Ts, mg_domain a S) tye
    and meets (T :: Ts, S :: Ss) tye = meets (Ts, Ss) (meet (devar tye T, S) tye)
      | meets _ tye = tye;

    fun unif (ty1, ty2) tye =
      (case (devar tye ty1, devar tye ty2) of
        (T as TVar (v, S1), U as TVar (w, S2)) =>
          if eq_ix (v, w) then
            if S1 = S2 then tye else tvar_clash v S1 S2
          else if Sorts.sort_le classes (S1, S2) then
            Vartab.update_new (w, (S2, T)) tye
          else if Sorts.sort_le classes (S2, S1) then
            Vartab.update_new (v, (S1, U)) tye
          else
            let val S = gen_tyvar (Sorts.inter_sort classes (S1, S2)) in
              Vartab.update_new (v, (S1, S)) (Vartab.update_new (w, (S2, S)) tye)
            end
      | (TVar (v, S), T) =>
          if occurs v tye T then raise TUNIFY
          else meet (T, S) (Vartab.update_new (v, (S, T)) tye)
      | (T, TVar (v, S)) =>
          if occurs v tye T then raise TUNIFY
          else meet (T, S) (Vartab.update_new (v, (S, T)) tye)
      | (Type (a, Ts), Type (b, Us)) =>
          if a <> b then raise TUNIFY
          else unifs (Ts, Us) tye
      | (T, U) => if T = U then tye else raise TUNIFY)
    and unifs (T :: Ts, U :: Us) tye = unifs (Ts, Us) (unif (T, U) tye)
      | unifs _ tye = tye;
  in (unif TU tyenv, ! tyvar_count) end;

(*purely structural unification*)
fun raw_unify (ty1, ty2) tye =
  (case (devar tye ty1, devar tye ty2) of
    (T as TVar (v, S1), U as TVar (w, S2)) =>
      if eq_ix (v, w) then
        if S1 = S2 then tye else tvar_clash v S1 S2
      else Vartab.update_new (w, (S2, T)) tye
  | (TVar (v, S), T) =>
      if occurs v tye T then raise TUNIFY
      else Vartab.update_new (v, (S, T)) tye
  | (T, TVar (v, S)) =>
      if occurs v tye T then raise TUNIFY
      else Vartab.update_new (v, (S, T)) tye
  | (Type (a, Ts), Type (b, Us)) =>
      if a <> b then raise TUNIFY
      else raw_unifys (Ts, Us) tye
  | (T, U) => if T = U then tye else raise TUNIFY)
and raw_unifys (T :: Ts, U :: Us) tye = raw_unifys (Ts, Us) (raw_unify (T, U) tye)
  | raw_unifys _ tye = tye;

(*fast unification filter*)
fun could_unify (Type (a, Ts), Type (b, Us)) = a = b andalso could_unifys (Ts, Us)
  | could_unify (TFree (a, _), TFree (b, _)) = a = b
  | could_unify (TVar _, _) = true
  | could_unify (_, TVar _) = true
  | could_unify _ = false
and could_unifys (T :: Ts, U :: Us) = could_unify (T, U) andalso could_unifys (Ts, Us)
  | could_unifys _ = true;


(*equality with respect to a type environment*)
fun eq_type tye (T, T') =
  (case (devar tye T, devar tye T') of
     (Type (s, Ts), Type (s', Ts')) =>
       s = s' andalso ListPair.all (eq_type tye) (Ts, Ts')
   | (U, U') => U = U');



(** extend and merge type signatures **)

(* classes *)

fun add_class pp naming (c, cs) tsig =
  tsig |> map_tsig (fn ((space, classes), default, types, arities) =>
    let
      val c' = NameSpace.full naming c;
      val cs' = map (cert_class tsig) cs
        handle TYPE (msg, _, _) => error msg;
      val space' = space |> NameSpace.declare naming c';
      val classes' = classes |> Sorts.add_class pp (c', cs');
    in ((space', classes'), default, types, arities) end);

fun hide_classes fully cs = map_tsig (fn ((space, classes), default, types, arities) =>
  ((fold (NameSpace.hide fully) cs space, classes), default, types, arities));


(* arities *)

fun add_arity pp (t, Ss, S) tsig = tsig |> map_tsig (fn (classes, default, types, arities) =>
  let
    val _ =
      (case Symtab.lookup (#2 types) t of
        SOME (LogicalType n, _) => if length Ss <> n then error (bad_nargs t) else ()
      | SOME (decl, _) => error ("Illegal " ^ str_of_decl decl ^ ": " ^ quote t)
      | NONE => error (undecl_type t));
    val (Ss', S') = (map (cert_sort tsig) Ss, cert_sort tsig S)
      handle TYPE (msg, _, _) => error msg;
    val arities' = arities |> Sorts.add_arities pp (#2 classes) ((t, map (fn c' => (c', Ss')) S'));
  in (classes, default, types, arities') end);


(* classrel *)

fun add_classrel pp rel tsig =
  tsig |> map_tsig (fn ((space, classes), default, types, arities) =>
    let
      val rel' = pairself (cert_class tsig) rel
        handle TYPE (msg, _, _) => error msg;
      val classes' = classes |> Sorts.add_classrel pp rel;
      val default' = default |> Sorts.norm_sort classes';
      val arities' = arities |> Sorts.rebuild_arities pp classes';
    in ((space, classes'), default', types, arities') end);


(* default sort *)

fun set_defsort S tsig = tsig |> map_tsig (fn (classes, _, types, arities) =>
  (classes, cert_sort tsig S handle TYPE (msg, _, _) => error msg, types, arities));


(* types *)

local

fun err_neg_args c =
  error ("Negative number of arguments in type constructor declaration: " ^ quote c);

fun err_in_decls c decl decl' =
  let val s = str_of_decl decl and s' = str_of_decl decl' in
    if s = s' then error ("Duplicate declaration of " ^ s ^ ": " ^ quote c)
    else error ("Conflict of " ^ s ^ " with " ^ s' ^ ": " ^ quote c)
  end;

fun new_decl naming (c, decl) (space, types) =
  let
    val c' = NameSpace.full naming c;
    val space' = NameSpace.declare naming c' space;
    val types' =
      (case Symtab.lookup types c' of
        SOME (decl', _) => err_in_decls c' decl decl'
      | NONE => Symtab.update (c', (decl, stamp ())) types);
  in (space', types') end;

fun the_decl (_, types) = fst o the o Symtab.lookup types;

fun change_types f = map_tsig (fn (classes, default, types, arities) =>
  (classes, default, f types, arities));

fun syntactic types (Type (c, Ts)) =
      (case Symtab.lookup types c of SOME (Nonterminal, _) => true | _ => false)
        orelse exists (syntactic types) Ts
  | syntactic _ _ = false;

fun add_abbrev naming (a, vs, rhs) tsig = tsig |> change_types (fn types =>
  let
    fun err msg = cat_error msg ("The error(s) above occurred in type abbreviation: " ^ quote a);
    val rhs' = strip_sorts (no_tvars (cert_typ_syntax tsig rhs))
      handle TYPE (msg, _, _) => err msg;
  in
    (case duplicates (op =) vs of
      [] => []
    | dups => err ("Duplicate variables on lhs: " ^ commas_quote dups));
    (case gen_rems (op =) (map (#1 o #1) (typ_tvars rhs'), vs) of
      [] => []
    | extras => err ("Extra variables on rhs: " ^ commas_quote extras));
    types |> new_decl naming (a, Abbreviation (vs, rhs', syntactic (#2 types) rhs'))
  end);

in

fun add_types naming ps = change_types (fold (new_decl naming) (ps |> map (fn (c, n) =>
  if n < 0 then err_neg_args c else (c, LogicalType n))));

val add_abbrevs = fold o add_abbrev;

fun add_nonterminals naming = change_types o fold (new_decl naming) o map (rpair Nonterminal);

fun merge_types (types1, types2) =
  NameSpace.merge_tables (Library.eq_snd (op =)) (types1, types2) handle Symtab.DUPS (d :: _) =>
    err_in_decls d (the_decl types1 d) (the_decl types2 d);

end;

fun hide_types fully cs = map_tsig (fn (classes, default, (space, types), arities) =>
  (classes, default, (fold (NameSpace.hide fully) cs space, types), arities));


(* merge type signatures *)

fun merge_tsigs pp (tsig1, tsig2) =
  let
    val (TSig {classes = (space1, classes1), default = default1, types = types1,
      arities = arities1, log_types = _, witness = _}) = tsig1;
    val (TSig {classes = (space2, classes2), default = default2, types = types2,
      arities = arities2, log_types = _, witness = _}) = tsig2;

    val space' = NameSpace.merge (space1, space2);
    val classes' = Sorts.merge_classes pp (classes1, classes2);
    val default' = Sorts.inter_sort classes' (default1, default2);
    val types' = merge_types (types1, types2);
    val arities' = Sorts.merge_arities pp classes' (arities1, arities2);
  in build_tsig ((space', classes'), default', types', arities') end;

end;
