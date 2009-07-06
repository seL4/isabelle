(*  Title:      Pure/type.ML
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
   {classes: NameSpace.T * Sorts.algebra,
    default: sort,
    types: ((decl * Properties.T) * serial) NameSpace.table,
    log_types: string list}
  val empty_tsig: tsig
  val defaultS: tsig -> sort
  val logical_types: tsig -> string list
  val eq_sort: tsig -> sort * sort -> bool
  val subsort: tsig -> sort * sort -> bool
  val of_sort: tsig -> typ * sort -> bool
  val inter_sort: tsig -> sort * sort -> sort
  val cert_class: tsig -> class -> class
  val cert_sort: tsig -> sort -> sort
  val witness_sorts: tsig -> (typ * sort) list -> sort list -> (typ * sort) list
  type mode
  val mode_default: mode
  val mode_syntax: mode
  val mode_abbrev: mode
  val get_mode: Proof.context -> mode
  val set_mode: mode -> Proof.context -> Proof.context
  val restore_mode: Proof.context -> Proof.context -> Proof.context
  val cert_typ_mode: mode -> tsig -> typ -> typ
  val cert_typ: tsig -> typ -> typ
  val arity_number: tsig -> string -> int
  val arity_sorts: Pretty.pp -> tsig -> string -> sort -> sort list
  val the_tags: tsig -> string -> Properties.T

  (*special treatment of type vars*)
  val strip_sorts: typ -> typ
  val similar_types: term * term -> bool
  val no_tvars: typ -> typ
  val varify: (string * sort) list -> term -> ((string * sort) * indexname) list * term
  val freeze_thaw_type: typ -> typ * (typ -> typ)
  val freeze_type: typ -> typ
  val freeze_thaw: term -> term * (term -> term)
  val freeze: term -> term

  (*matching and unification*)
  exception TYPE_MATCH
  type tyenv = (sort * typ) Vartab.table
  val lookup: tyenv -> indexname * sort -> typ option
  val typ_match: tsig -> typ * typ -> tyenv -> tyenv
  val typ_instance: tsig -> typ * typ -> bool
  val raw_match: typ * typ -> tyenv -> tyenv
  val raw_matches: typ list * typ list -> tyenv -> tyenv
  val raw_instance: typ * typ -> bool
  exception TUNIFY
  val unify: tsig -> typ * typ -> tyenv * int -> tyenv * int
  val raw_unify: typ * typ -> tyenv -> tyenv
  val raw_unifys: typ list * typ list -> tyenv -> tyenv
  val could_unify: typ * typ -> bool
  val could_unifys: typ list * typ list -> bool
  val eq_type: tyenv -> typ * typ -> bool

  (*extend and merge type signatures*)
  val add_class: Pretty.pp -> NameSpace.naming -> binding * class list -> tsig -> tsig
  val hide_class: bool -> string -> tsig -> tsig
  val set_defsort: sort -> tsig -> tsig
  val add_type: NameSpace.naming -> Properties.T -> binding * int -> tsig -> tsig
  val add_abbrev: NameSpace.naming -> Properties.T -> binding * string list * typ -> tsig -> tsig
  val add_nonterminal: NameSpace.naming -> Properties.T -> binding -> tsig -> tsig
  val hide_type: bool -> string -> tsig -> tsig
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
    classes: NameSpace.T * Sorts.algebra,   (*order-sorted algebra of type classes*)
    default: sort,                          (*default sort on input*)
    types: ((decl * Properties.T) * serial) NameSpace.table, (*declared types*)
    log_types: string list};                (*logical types sorted by number of arguments*)

fun rep_tsig (TSig comps) = comps;

fun make_tsig (classes, default, types, log_types) =
  TSig {classes = classes, default = default, types = types, log_types = log_types};

fun build_tsig ((space, classes), default, types) =
  let
    val log_types =
      Symtab.fold (fn (c, ((LogicalType n, _), _)) => cons (c, n) | _ => I) (snd types) []
      |> Library.sort (Library.int_ord o pairself snd) |> map fst;
  in make_tsig ((space, classes), default, types, log_types) end;

fun map_tsig f (TSig {classes, default, types, log_types = _}) =
  build_tsig (f (classes, default, types));

val empty_tsig =
  build_tsig ((NameSpace.empty, Sorts.empty_algebra), [], NameSpace.empty_table);


(* classes and sorts *)

fun defaultS (TSig {default, ...}) = default;
fun logical_types (TSig {log_types, ...}) = log_types;

fun eq_sort (TSig {classes, ...}) = Sorts.sort_eq (#2 classes);
fun subsort (TSig {classes, ...}) = Sorts.sort_le (#2 classes);
fun of_sort (TSig {classes, ...}) = Sorts.of_sort (#2 classes);
fun inter_sort (TSig {classes, ...}) = Sorts.inter_sort (#2 classes);

fun cert_class (TSig {classes, ...}) = Sorts.certify_class (#2 classes);
fun cert_sort (TSig {classes, ...}) = Sorts.certify_sort (#2 classes);

fun witness_sorts (tsig as TSig {classes, log_types, ...}) =
  Sorts.witness_sorts (#2 classes) log_types;


(* certification mode *)

datatype mode = Mode of {normalize: bool, logical: bool};

val mode_default = Mode {normalize = true, logical = true};
val mode_syntax = Mode {normalize = true, logical = false};
val mode_abbrev = Mode {normalize = false, logical = false};

structure Mode = ProofDataFun
(
  type T = mode;
  fun init _ = mode_default;
);

val get_mode = Mode.get;
fun set_mode mode = Mode.map (K mode);
fun restore_mode ctxt = set_mode (get_mode ctxt);


(* lookup types *)

fun undecl_type c = "Undeclared type constructor: " ^ quote c;

fun lookup_type (TSig {types, ...}) = Option.map fst o Symtab.lookup (snd types);

fun the_tags tsig c =
  (case lookup_type tsig c of
    SOME (_, tags) => tags
  | NONE => error (undecl_type c));


(* certified types *)

fun bad_nargs t = "Bad number of arguments for type constructor: " ^ quote t;

local

fun inst_typ env (Type (c, Ts)) = Type (c, map (inst_typ env) Ts)
  | inst_typ env (T as TFree (x, _)) = the_default T (AList.lookup (op =) env x)
  | inst_typ _ T = T;

in

fun cert_typ_mode (Mode {normalize, logical}) tsig ty =
  let
    fun err msg = raise TYPE (msg, [ty], []);

    val check_logical =
      if logical then fn c => err ("Illegal occurrence of syntactic type: " ^ quote c)
      else fn _ => ();

    fun cert (T as Type (c, Ts)) =
          let
            val Ts' = map cert Ts;
            fun nargs n = if length Ts <> n then err (bad_nargs c) else ();
          in
            (case lookup_type tsig c of
              SOME (LogicalType n, _) => (nargs n; Type (c, Ts'))
            | SOME (Abbreviation (vs, U, syn), _) =>
               (nargs (length vs);
                if syn then check_logical c else ();
                if normalize then inst_typ (vs ~~ Ts') U
                else Type (c, Ts'))
            | SOME (Nonterminal, _) => (nargs 0; check_logical c; T)
            | NONE => err (undecl_type c))
          end
      | cert (TFree (x, S)) = TFree (x, cert_sort tsig S)
      | cert (TVar (xi as (_, i), S)) =
          if i < 0 then
            err ("Malformed type variable: " ^ quote (Term.string_of_vname xi))
          else TVar (xi, cert_sort tsig S);

    val ty' = cert ty;
  in if ty = ty' then ty else ty' end;  (*avoid copying of already normal type*)

val cert_typ = cert_typ_mode mode_default;

end;


(* type arities *)

fun arity_number tsig a =
  (case lookup_type tsig a of
    SOME (LogicalType n, _) => n
  | _ => error (undecl_type a));

fun arity_sorts _ tsig a [] = replicate (arity_number tsig a) []
  | arity_sorts pp (TSig {classes, ...}) a S = Sorts.mg_domain (#2 classes) a S
      handle Sorts.CLASS_ERROR err => error (Sorts.class_error pp err);



(** special treatment of type vars **)

(* strip_sorts *)

fun strip_sorts (Type (a, Ts)) = Type (a, map strip_sorts Ts)
  | strip_sorts (TFree (x, _)) = TFree (x, [])
  | strip_sorts (TVar (xi, _)) = TVar (xi, []);


(* equivalence up to renaming of atomic types *)

local

fun standard_types t =
  let
    val Ts = fold_types (fold_atyps (insert (op =))) t [];
    val Ts' = map (fn a => TFree (a, [])) (Name.invents Name.context Name.aT (length Ts));
  in map_types (map_atyps (perhaps (AList.lookup (op =) (Ts ~~ Ts')))) t end;

in

val similar_types = op aconv o pairself (Term.map_types strip_sorts o standard_types);

end;


(* no_tvars *)

fun no_tvars T =
  (case Term.add_tvarsT T [] of [] => T
  | vs => raise TYPE ("Illegal schematic type variable(s): " ^
      commas_quote (map (Term.string_of_vname o #1) (rev vs)), [T], []));


(* varify *)

fun varify fixed t =
  let
    val fs = Term.fold_types (Term.fold_atyps
      (fn TFree v => if member (op =) fixed v then I else insert (op =) v | _ => I)) t [];
    val used = Name.context
      |> fold_types (fold_atyps (fn TVar ((a, _), _) => Name.declare a | _ => I)) t;
    val fmap = fs ~~ map (rpair 0) (#1 (Name.variants (map fst fs) used));
    fun thaw (f as (a, S)) =
      (case AList.lookup (op =) fmap f of
        NONE => TFree f
      | SOME xi => TVar (xi, S));
  in (fmap, map_types (map_type_tfree thaw) t) end;


(* freeze_thaw: freeze TVars in a term; return the "thaw" inverse *)

local

fun new_name (ix, (pairs, used)) =
  let val v = Name.variant used (string_of_indexname ix)
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
    val used = OldTerm.add_typ_tfree_names (T, [])
    and tvars = map #1 (OldTerm.add_typ_tvars (T, []));
    val (alist, _) = List.foldr new_name ([], used) tvars;
  in (map_type_tvar (freeze_one alist) T, map_type_tfree (thaw_one (map swap alist))) end;

val freeze_type = #1 o freeze_thaw_type;

fun freeze_thaw t =
  let
    val used = OldTerm.it_term_types OldTerm.add_typ_tfree_names (t, [])
    and tvars = map #1 (OldTerm.it_term_types OldTerm.add_typ_tvars (t, []));
    val (alist, _) = List.foldr new_name ([], used) tvars;
  in
    (case alist of
      [] => (t, fn x => x) (*nothing to do!*)
    | _ => (map_types (map_type_tvar (freeze_one alist)) t,
      map_types (map_type_tfree (thaw_one (map swap alist)))))
  end;

val freeze = #1 o freeze_thaw;

end;



(** matching and unification of types **)

type tyenv = (sort * typ) Vartab.table;

fun tvar_clash ixn S S' = raise TYPE ("Type variable " ^
  quote (Term.string_of_vname ixn) ^ " has two distinct sorts",
  [TVar (ixn, S), TVar (ixn, S')], []);

fun lookup tye (ixn, S) =
  (case Vartab.lookup tye ixn of
    NONE => NONE
  | SOME (S', T) => if S = S' then SOME T else tvar_clash ixn S S');


(* matching *)

exception TYPE_MATCH;

fun typ_match tsig =
  let
    fun match (TVar (v, S), T) subs =
          (case lookup subs (v, S) of
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
      (case lookup subs (v, S) of
        NONE => Vartab.update_new (v, (S, T)) subs
      | SOME U => if U = T then subs else raise TYPE_MATCH)
  | raw_match (Type (a, Ts), Type (b, Us)) subs =
      if a <> b then raise TYPE_MATCH
      else raw_matches (Ts, Us) subs
  | raw_match (TFree x, TFree y) subs =
      if x = y then subs else raise TYPE_MATCH
  | raw_match _ _ = raise TYPE_MATCH
and raw_matches (T :: Ts, U :: Us) subs = raw_matches (Ts, Us) (raw_match (T, U) subs)
  | raw_matches ([], []) subs = subs
  | raw_matches _ _ = raise TYPE_MATCH;

fun raw_instance (T, U) =
  (raw_match (U, T) Vartab.empty; true) handle TYPE_MATCH => false;


(* unification *)

exception TUNIFY;

(*occurs check*)
fun occurs v tye =
  let
    fun occ (Type (_, Ts)) = exists occ Ts
      | occ (TFree _) = false
      | occ (TVar (w, S)) =
          Term.eq_ix (v, w) orelse
            (case lookup tye (w, S) of
              NONE => false
            | SOME U => occ U);
  in occ end;

(*chase variable assignments; if devar returns a type var then it must be unassigned*)
fun devar tye (T as TVar v) =
      (case lookup tye v of
        SOME U => devar tye U
      | NONE => T)
  | devar tye T = T;

(*order-sorted unification*)
fun unify (tsig as TSig {classes = (_, classes), ...}) TU (tyenv, maxidx) =
  let
    val tyvar_count = ref maxidx;
    fun gen_tyvar S = TVar ((Name.aT, inc tyvar_count), S);

    fun mg_domain a S = Sorts.mg_domain classes a S
      handle Sorts.CLASS_ERROR _ => raise TUNIFY;

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
          if Term.eq_ix (v, w) then
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
      if Term.eq_ix (v, w) then
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
  | raw_unifys ([], []) tye = tye
  | raw_unifys _ _ = raise TUNIFY;

(*fast unification filter*)
fun could_unify (Type (a, Ts), Type (b, Us)) = a = b andalso could_unifys (Ts, Us)
  | could_unify (TFree (a, _), TFree (b, _)) = a = b
  | could_unify (TVar _, _) = true
  | could_unify (_, TVar _) = true
  | could_unify _ = false
and could_unifys (T :: Ts, U :: Us) = could_unify (T, U) andalso could_unifys (Ts, Us)
  | could_unifys ([], []) = true
  | could_unifys _ = false;


(*equality with respect to a type environment*)
fun eq_type tye (T, T') =
  (case (devar tye T, devar tye T') of
     (Type (s, Ts), Type (s', Ts')) =>
       s = s' andalso ListPair.all (eq_type tye) (Ts, Ts')
   | (U, U') => U = U');



(** extend and merge type signatures **)

(* classes *)

fun add_class pp naming (c, cs) tsig =
  tsig |> map_tsig (fn ((space, classes), default, types) =>
    let
      val cs' = map (cert_class tsig) cs
        handle TYPE (msg, _, _) => error msg;
      val (c', space') = space |> NameSpace.declare naming c;
      val classes' = classes |> Sorts.add_class pp (c', cs');
    in ((space', classes'), default, types) end);

fun hide_class fully c = map_tsig (fn ((space, classes), default, types) =>
  ((NameSpace.hide fully c space, classes), default, types));


(* arities *)

fun add_arity pp (t, Ss, S) tsig = tsig |> map_tsig (fn ((space, classes), default, types) =>
  let
    val _ =
      (case lookup_type tsig t of
        SOME (LogicalType n, _) => if length Ss <> n then error (bad_nargs t) else ()
      | SOME (decl, _) => error ("Illegal " ^ str_of_decl decl ^ ": " ^ quote t)
      | NONE => error (undecl_type t));
    val (Ss', S') = (map (cert_sort tsig) Ss, cert_sort tsig S)
      handle TYPE (msg, _, _) => error msg;
    val classes' = classes |> Sorts.add_arities pp ((t, map (fn c' => (c', Ss')) S'));
  in ((space, classes'), default, types) end);


(* classrel *)

fun add_classrel pp rel tsig =
  tsig |> map_tsig (fn ((space, classes), default, types) =>
    let
      val rel' = pairself (cert_class tsig) rel
        handle TYPE (msg, _, _) => error msg;
      val classes' = classes |> Sorts.add_classrel pp rel;
    in ((space, classes'), default, types) end);


(* default sort *)

fun set_defsort S tsig = tsig |> map_tsig (fn (classes, _, types) =>
  (classes, cert_sort tsig S handle TYPE (msg, _, _) => error msg, types));


(* types *)

local

fun err_in_decls c decl decl' =
  let val s = str_of_decl decl and s' = str_of_decl decl' in
    if s = s' then error ("Duplicate declaration of " ^ s ^ ": " ^ quote c)
    else error ("Conflict of " ^ s ^ " with " ^ s' ^ ": " ^ quote c)
  end;

fun new_decl naming tags (c, decl) (space, types) =
  let
    val tags' = tags |> Position.default_properties (Position.thread_data ());
    val (c', space') = NameSpace.declare naming c space;
    val types' =
      (case Symtab.lookup types c' of
        SOME ((decl', _), _) => err_in_decls c' decl decl'
      | NONE => Symtab.update (c', ((decl, tags'), serial ())) types);
  in (space', types') end;

fun the_decl (_, types) = fst o fst o the o Symtab.lookup types;

fun map_types f = map_tsig (fn (classes, default, types) =>
  let
    val (space', tab') = f types;
    val _ = NameSpace.intern space' "dummy" = "dummy" orelse
      error "Illegal declaration of dummy type";
  in (classes, default, (space', tab')) end);

fun syntactic types (Type (c, Ts)) =
      (case Symtab.lookup types c of SOME ((Nonterminal, _), _) => true | _ => false)
        orelse exists (syntactic types) Ts
  | syntactic _ _ = false;

in

fun add_type naming tags (c, n) =
  if n < 0 then error ("Bad type constructor declaration: " ^ quote (Binding.str_of c))
  else map_types (new_decl naming tags (c, LogicalType n));

fun add_abbrev naming tags (a, vs, rhs) tsig = tsig |> map_types (fn types =>
  let
    fun err msg =
      cat_error msg ("The error(s) above occurred in type abbreviation: " ^ quote (Binding.str_of a));
    val rhs' = strip_sorts (no_tvars (cert_typ_mode mode_syntax tsig rhs))
      handle TYPE (msg, _, _) => err msg;
  in
    (case duplicates (op =) vs of
      [] => []
    | dups => err ("Duplicate variables on lhs: " ^ commas_quote dups));
    (case subtract (op =) vs (map #1 (Term.add_tfreesT rhs' [])) of
      [] => []
    | extras => err ("Extra variables on rhs: " ^ commas_quote extras));
    types |> new_decl naming tags (a, Abbreviation (vs, rhs', syntactic (#2 types) rhs'))
  end);

fun add_nonterminal naming tags = map_types o new_decl naming tags o rpair Nonterminal;

fun merge_types (types1, types2) =
  NameSpace.merge_tables (Library.eq_snd (op = : serial * serial -> bool)) (types1, types2)
    handle Symtab.DUP d => err_in_decls d (the_decl types1 d) (the_decl types2 d);

end;

fun hide_type fully c = map_tsig (fn (classes, default, (space, types)) =>
  (classes, default, (NameSpace.hide fully c space, types)));


(* merge type signatures *)

fun merge_tsigs pp (tsig1, tsig2) =
  let
    val (TSig {classes = (space1, classes1), default = default1, types = types1,
      log_types = _}) = tsig1;
    val (TSig {classes = (space2, classes2), default = default2, types = types2,
      log_types = _}) = tsig2;

    val space' = NameSpace.merge (space1, space2);
    val classes' = Sorts.merge_algebra pp (classes1, classes2);
    val default' = Sorts.inter_sort classes' (default1, default2);
    val types' = merge_types (types1, types2);
  in build_tsig ((space', classes'), default', types') end;

end;
