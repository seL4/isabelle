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
    Abbreviation of string list * typ |
    Nonterminal
  type tsig
  val rep_tsig: tsig ->
   {classes: Sorts.classes,
    default: sort,
    types: (decl * stamp) Symtab.table,
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
  val cert_class: tsig -> class -> class
  val cert_sort: tsig -> sort -> sort
  val witness_sorts: tsig -> sort list -> sort list -> (typ * sort) list
  val norm_typ: tsig -> typ -> typ
  val cert_typ: tsig -> typ -> typ
  val cert_typ_syntax: tsig -> typ -> typ
  val cert_typ_raw: tsig -> typ -> typ

  (*special treatment of type vars*)
  val strip_sorts: typ -> typ
  val no_tvars: typ -> typ
  val varifyT: typ -> typ
  val unvarifyT: typ -> typ
  val varify: term * string list -> term * (string * indexname) list
  val freeze_thaw_type : typ -> typ * (typ -> typ)
  val freeze_thaw : term -> term * (term -> term)

  (*matching and unification*)
  val inst_term_tvars: tsig -> (indexname * typ) list -> term -> term
  val inst_typ_tvars: tsig -> (indexname * typ) list -> typ -> typ
  exception TYPE_MATCH
  val typ_match: tsig -> typ Vartab.table * (typ * typ) -> typ Vartab.table
  val typ_instance: tsig -> typ * typ -> bool
  exception TUNIFY
  val unify: tsig -> typ Vartab.table * int -> typ * typ -> typ Vartab.table * int
  val raw_unify: typ * typ -> bool

  (*extend and merge type signatures*)
  val add_classes: (class * class list) list -> tsig -> tsig
  val add_classrel: (class * class) list -> tsig -> tsig
  val set_defsort: sort -> tsig -> tsig
  val add_types: (string * int) list -> tsig -> tsig
  val add_abbrs: (string * string list * typ) list -> tsig -> tsig
  val add_nonterminals: string list -> tsig -> tsig
  val add_arities: (string * sort list * sort) list -> tsig -> tsig
  val merge_tsigs: tsig * tsig -> tsig
end;

structure Type: TYPE =
struct

(** type signatures and certified types **)

(* type declarations *)

datatype decl =
  LogicalType of int |
  Abbreviation of string list * typ |
  Nonterminal;

fun str_of_decl (LogicalType _) = "logical type constructor"
  | str_of_decl (Abbreviation _) = "type abbreviation"
  | str_of_decl Nonterminal = "syntactic type";


(* type tsig *)

datatype tsig =
  TSig of {
    classes: Sorts.classes,              (*declared classes with proper subclass relation*)
    default: sort,                       (*default sort on input*)
    types: (decl * stamp) Symtab.table,  (*declared types*)
    arities: Sorts.arities,              (*image specification of types wrt. sorts*)
    log_types: string list,              (*logical types sorted by number of arguments*)
    witness: (typ * sort) option};       (*witness for non-emptiness of strictest sort*)

fun rep_tsig (TSig comps) = comps;

fun make_tsig (classes, default, types, arities, log_types, witness) =
  TSig {classes = classes, default = default, types = types, arities = arities,
    log_types = log_types, witness = witness};

fun map_tsig f (TSig {classes, default, types, arities, log_types, witness}) =
  make_tsig (f (classes, default, types, arities, log_types, witness));

fun build_tsig (classes, default, types, arities) =
  let
    fun add_log_type (ts, (c, (LogicalType n, _))) = (c, n) :: ts
      | add_log_type (ts, _) = ts;
    val log_types =
      Symtab.foldl add_log_type ([], types)
      |> Library.sort (Library.int_ord o pairself #2) |> map #1;
    val witness =
      (case Sorts.witness_sorts (classes, arities) log_types [] [Graph.keys classes] of
        [w] => Some w | _ => None);
  in make_tsig (classes, default, types, arities, log_types, witness) end;

fun change_tsig f (TSig {classes, default, types, arities, log_types = _, witness = _}) =
  build_tsig (f (classes, default, types, arities));

val empty_tsig = build_tsig (Graph.empty, [], Symtab.empty, Symtab.empty);


(* classes and sorts *)

fun classes (TSig {classes = C, ...}) = Graph.keys C;
fun defaultS (TSig {default, ...}) = default;
fun logical_types (TSig {log_types, ...}) = log_types;
fun universal_witness (TSig {witness, ...}) = witness;

fun eq_sort (TSig {classes, ...}) = Sorts.sort_eq classes;
fun subsort (TSig {classes, ...}) = Sorts.sort_le classes;
fun of_sort (TSig {classes, arities, ...}) = Sorts.of_sort (classes, arities);
fun norm_sort (TSig {classes, ...}) = Sorts.norm_sort classes;

fun cert_class (TSig {classes, ...}) c =
  if can (Graph.get_node classes) c then c
  else raise TYPE ("Undeclared class: " ^ quote c, [], []);

fun cert_sort tsig = norm_sort tsig o map (cert_class tsig);

fun witness_sorts (tsig as TSig {classes, arities, log_types, ...}) =
  Sorts.witness_sorts (classes, arities) log_types;


(* certified types *)

fun bad_nargs t = "Bad number of arguments for type constructor: " ^ quote t;

fun inst_typ tye =
  let
    fun inst (var as (v, _)) =
      (case assoc_string_int (tye, v) of
        Some U => inst_typ tye U
      | None => TVar var);
  in map_type_tvar inst end;

(*expand type abbreviations and normalize sorts*)
fun norm_typ (tsig as TSig {types, ...}) ty =
  let
    val idx = Term.maxidx_of_typ ty + 1;

    fun norm (Type (a, Ts)) =
          (case Symtab.lookup (types, a) of
            Some (Abbreviation (vs, U), _) =>
              norm (inst_typ (map (rpair idx) vs ~~ Ts) (incr_tvar idx U))
          | _ => Type (a, map norm Ts))
      | norm (TFree (x, S)) = TFree (x, norm_sort tsig S)
      | norm (TVar (xi, S)) = TVar (xi, norm_sort tsig S);

    val ty' = norm ty;
  in if ty = ty' then ty else ty' end;  (*avoid copying of already normal type*)

(*check validity of (not necessarily normal) type*)   (*exception TYPE*)
fun certify_typ normalize syntax tsig ty =
  let
    val TSig {types, ...} = tsig;
    fun err msg = raise TYPE (msg, [ty], []);

    fun check_sort S = (map (cert_class tsig) S; ());

    fun check_typ (Type (c, Ts)) =
          let fun nargs n = if length Ts <> n then err (bad_nargs c) else () in
            (case Symtab.lookup (types, c) of
              Some (LogicalType n, _) => nargs n
            | Some (Abbreviation (vs, _), _) => nargs (length vs)
            | Some (Nonterminal, _) => nargs 0
            | None => err ("Undeclared type constructor: " ^ quote c));
            seq check_typ Ts
          end
    | check_typ (TFree (_, S)) = check_sort S
    | check_typ (TVar ((x, i), S)) =
        if i < 0 then err ("Malformed type variable: " ^ quote (Term.string_of_vname (x, i)))
        else check_sort S;

    fun no_syntax (Type (c, Ts)) =
          (case Symtab.lookup (types, c) of
            Some (Nonterminal, _) =>
              err ("Illegal occurrence of syntactic type: " ^ quote c)
          | _ => seq no_syntax Ts)
      | no_syntax _ = ();

    val _ = check_typ ty;
    val ty' = if normalize orelse not syntax then norm_typ tsig ty else ty;
    val _ = if not syntax then no_syntax ty' else ();
  in ty' end;

val cert_typ         = certify_typ true false;
val cert_typ_syntax  = certify_typ true true;
val cert_typ_raw     = certify_typ false true;



(** special treatment of type vars **)

(* strip_sorts *)

fun strip_sorts (Type (a, Ts)) = Type (a, map strip_sorts Ts)
  | strip_sorts (TFree (x, _)) = TFree (x, [])
  | strip_sorts (TVar (xi, _)) = TVar (xi, []);


(* no_tvars *)

fun no_tvars T =
  (case typ_tvars T of [] => T
  | vs => raise TYPE ("Illegal schematic type variable(s): " ^
      commas (map (Term.string_of_vname o #1) vs), [T], []));


(* varify, unvarify *)

val varifyT = map_type_tfree (fn (a, S) => TVar ((a, 0), S));

fun unvarifyT (Type (a, Ts)) = Type (a, map unvarifyT Ts)
  | unvarifyT (TVar ((a, 0), S)) = TFree (a, S)
  | unvarifyT T = T;

fun varify (t, fixed) =
  let
    val fs = add_term_tfree_names (t, []) \\ fixed;
    val ixns = add_term_tvar_ixns (t, []);
    val fmap = fs ~~ map (rpair 0) (variantlist (fs, map #1 ixns))
    fun thaw (f as (a, S)) =
      (case assoc (fmap, a) of
        None => TFree f
      | Some b => TVar (b, S));
  in (map_term_types (map_type_tfree thaw) t, fmap) end;


(* freeze_thaw: freeze TVars in a term; return the "thaw" inverse *)

local

fun new_name (ix, (pairs,used)) =
      let val v = variant used (string_of_indexname ix)
      in  ((ix,v)::pairs, v::used)  end;

fun freeze_one alist (ix,sort) =
  TFree (the (assoc (alist, ix)), sort)
    handle OPTION =>
      raise TYPE ("Failure during freezing of ?" ^ string_of_indexname ix, [], []);

fun thaw_one alist (a,sort) = TVar (the (assoc (alist,a)), sort)
      handle OPTION => TFree(a,sort);

in

(*this sort of code could replace unvarifyT*)
fun freeze_thaw_type T =
  let
    val used = add_typ_tfree_names (T, [])
    and tvars = map #1 (add_typ_tvars (T, []));
    val (alist, _) = foldr new_name (tvars, ([], used));
  in (map_type_tvar (freeze_one alist) T, map_type_tfree (thaw_one (map swap alist))) end;

fun freeze_thaw t =
  let
    val used = it_term_types add_typ_tfree_names (t, [])
    and tvars = map #1 (it_term_types add_typ_tvars (t, []));
    val (alist, _) = foldr new_name (tvars, ([], used));
  in
    (case alist of
      [] => (t, fn x => x) (*nothing to do!*)
    | _ => (map_term_types (map_type_tvar (freeze_one alist)) t,
      map_term_types (map_type_tfree (thaw_one (map swap alist)))))
  end;

end;



(** matching and unification of types **)

(* instantiation *)

fun type_of_sort tsig (T, S) =
  if of_sort tsig (T, S) then T
  else raise TYPE ("Type not of sort " ^ Sorts.str_of_sort S, [T], []);

fun inst_typ_tvars tsig tye =
  let
    fun inst (var as (v, S)) =
      (case assoc_string_int (tye, v) of
        Some U => type_of_sort tsig (U, S)
      | None => TVar var);
  in map_type_tvar inst end;

fun inst_term_tvars _ [] t = t
  | inst_term_tvars tsig tye t = map_term_types (inst_typ_tvars tsig tye) t;


(* matching *)

exception TYPE_MATCH;

fun typ_match tsig =
  let
    fun match (subs, (TVar (v, S), T)) =
          (case Vartab.lookup (subs, v) of
            None => (Vartab.update_new ((v, type_of_sort tsig (T, S)), subs)
              handle TYPE _ => raise TYPE_MATCH)
          | Some U => if U = T then subs else raise TYPE_MATCH)
      | match (subs, (Type (a, Ts), Type (b, Us))) =
          if a <> b then raise TYPE_MATCH
          else foldl match (subs, Ts ~~ Us)
      | match (subs, (TFree x, TFree y)) =
          if x = y then subs else raise TYPE_MATCH
      | match _ = raise TYPE_MATCH;
  in match end;

fun typ_instance tsig (T, U) =
  (typ_match tsig (Vartab.empty, (U, T)); true) handle TYPE_MATCH => false;


(* unification *)

exception TUNIFY;

(*occurs_check*)
fun occurs v tye =
  let
    fun occ (Type (_, Ts)) = exists occ Ts
      | occ (TFree _) = false
      | occ (TVar (w, _)) =
          eq_ix (v, w) orelse
            (case Vartab.lookup (tye, w) of
              None => false
            | Some U => occ U);
  in occ end;

(*chase variable assignments; if devar returns a type var then it must be unassigned*)
fun devar (T as TVar (v, _), tye) =
      (case  Vartab.lookup (tye, v) of
        Some U => devar (U, tye)
      | None => T)
  | devar (T, tye) = T;

fun unify (tsig as TSig {classes, arities, ...}) (tyenv, maxidx) TU =
  let
    val tyvar_count = ref maxidx;
    fun gen_tyvar S = TVar (("'a", inc tyvar_count), S);

    fun mg_domain a S =
      Sorts.mg_domain (classes, arities) a S handle Sorts.DOMAIN _ => raise TUNIFY;

    fun meet ((_, []), tye) = tye
      | meet ((TVar (xi, S'), S), tye) =
          if Sorts.sort_le classes (S', S) then tye
          else Vartab.update_new ((xi,
            gen_tyvar (Sorts.inter_sort classes (S', S))), tye)
      | meet ((TFree (_, S'), S), tye) =
          if Sorts.sort_le classes (S', S) then tye
          else raise TUNIFY
      | meet ((Type (a, Ts), S), tye) = meets ((Ts, mg_domain a S), tye)
    and meets (([], []), tye) = tye
      | meets ((T :: Ts, S :: Ss), tye) =
          meets ((Ts, Ss), meet ((devar (T, tye), S), tye))
      | meets _ = sys_error "meets";

    fun unif ((ty1, ty2), tye) =
      (case (devar (ty1, tye), devar (ty2, tye)) of
        (T as TVar (v, S1), U as TVar (w, S2)) =>
          if eq_ix (v, w) then tye
          else if Sorts.sort_le classes (S1, S2) then
            Vartab.update_new ((w, T), tye)
          else if Sorts.sort_le classes (S2, S1) then
            Vartab.update_new ((v, U), tye)
          else
            let val S = gen_tyvar (Sorts.inter_sort classes (S1, S2)) in
              Vartab.update_new ((v, S), Vartab.update_new ((w, S), tye))
            end
      | (TVar (v, S), T) =>
          if occurs v tye T then raise TUNIFY
          else meet ((T, S), Vartab.update_new ((v, T), tye))
      | (T, TVar (v, S)) =>
          if occurs v tye T then raise TUNIFY
          else meet ((T, S), Vartab.update_new ((v, T), tye))
      | (Type (a, Ts), Type (b, Us)) =>
          if a <> b then raise TUNIFY
          else foldr unif (Ts ~~ Us, tye)
      | (T, U) => if T = U then tye else raise TUNIFY);
  in (unif (TU, tyenv), ! tyvar_count) end;

(*purely structural unification *)
fun raw_unify (ty1, ty2) =
  (unify empty_tsig (Vartab.empty, 0) (strip_sorts ty1, strip_sorts ty2); true)
    handle TUNIFY => false;



(** extend and merge type signatures **)

(* arities *)

local

fun err_decl t decl = error ("Illegal " ^ str_of_decl decl ^ ": " ^ quote t);
fun err_undecl t = error ("Undeclared type constructor: " ^ quote t);

fun err_conflict t (c1, c2) (c, Ss) (c', Ss') =
  error ("Conflict of type arities for classes " ^ quote c1 ^ " < " ^ quote c2 ^ ":\n  " ^
    Sorts.str_of_arity (t, Ss, [c]) ^ " and\n  " ^
    Sorts.str_of_arity (t, Ss', [c']));

fun coregular C t (c, Ss) ars =
  let
    fun conflict (c', Ss') =
      if Sorts.class_le C (c, c') andalso not (Sorts.sorts_le C (Ss, Ss')) then
        Some ((c, c'), (c', Ss'))
      else if Sorts.class_le C (c', c) andalso not (Sorts.sorts_le C (Ss', Ss)) then
        Some ((c', c), (c', Ss'))
      else None;
  in
    (case Library.get_first conflict ars of
      Some ((c1, c2), (c', Ss')) => err_conflict t (c1, c2) (c, Ss) (c', Ss')
    | None => (c, Ss) :: ars)
  end;

fun insert C t ((c, Ss), ars) =
  (case assoc_string (ars, c) of
    None => coregular C t (c, Ss) ars
  | Some Ss' =>
      if Sorts.sorts_le C (Ss, Ss') then ars
      else if Sorts.sorts_le C (Ss', Ss)
      then coregular C t (c, Ss) (ars \ (c, Ss'))
      else coregular C t (c, Ss) ars);

fun complete C (c, Ss) = map (rpair Ss) (Graph.all_succs C [c]);

fun insert_arities classes (arities, (t, ars)) =
  let val ars' =
    Symtab.lookup_multi (arities, t)
    |> curry (foldr (insert classes t)) (flat (map (complete classes) ars))
  in Symtab.update ((t, ars'), arities) end;

fun insert_table classes = Symtab.foldl (fn (arities, (t, ars)) =>
  insert_arities classes (arities, (t, map (apsnd (map (Sorts.norm_sort classes))) ars)));

in

fun add_arities decls tsig = tsig |> change_tsig (fn (classes, default, types, arities) =>
  let
    fun prep (t, Ss, S) =
      (case Symtab.lookup (types, t) of
        Some (LogicalType n, _) =>
          if length Ss = n then
            (t, map (cert_sort tsig) Ss, cert_sort tsig S)
              handle TYPE (msg, _, _) => error msg
          else error (bad_nargs t)
      | Some (decl, _) => err_decl t decl
      | None => err_undecl t);

    val ars = decls |> map ((fn (t, Ss, S) => (t, map (fn c => (c, Ss)) S)) o prep);
    val arities' = foldl (insert_arities classes) (arities, ars);
  in (classes, default, types, arities') end);

fun rebuild_arities classes arities =
  insert_table classes (Symtab.empty, arities);

fun merge_arities classes (arities1, arities2) =
  insert_table classes (insert_table classes (Symtab.empty, arities1), arities2);

end;


(* classes *)

local

fun err_dup_classes cs =
  error ("Duplicate declaration of class(es): " ^ commas_quote cs);

fun err_cyclic_classes css =
  error (cat_lines (map (fn cs =>
    "Cycle in class relation: " ^ space_implode " < " (map quote cs)) css));

fun add_class (c, cs) tsig = tsig |> change_tsig (fn (classes, default, types, arities) =>
  let
    val cs' = map (cert_class tsig) cs
      handle TYPE (msg, _, _) => error msg;
    val classes' = classes |> Graph.new_node (c, stamp ())
      handle Graph.DUP d => err_dup_classes [d];
    val classes'' = classes' |> fold Graph.add_edge_trans_acyclic (map (pair c) cs')
      handle Graph.CYCLES css => err_cyclic_classes css;
  in (classes'', default, types, arities) end);

in

val add_classes = fold add_class;

fun add_classrel ps tsig = tsig |> change_tsig (fn (classes, default, types, arities) =>
  let
    val ps' = map (pairself (cert_class tsig)) ps
      handle TYPE (msg, _, _) => error msg;
    val classes' = classes |> fold Graph.add_edge_trans_acyclic ps'
      handle Graph.CYCLES css => err_cyclic_classes css;
    val default' = default |> Sorts.norm_sort classes';
    val arities' = arities |> rebuild_arities classes';
  in (classes', default', types, arities') end);

fun merge_classes CC = Graph.merge_trans_acyclic (op =) CC
  handle Graph.DUPS cs => err_dup_classes cs
    | Graph.CYCLES css => err_cyclic_classes css;

end;


(* default sort *)

fun set_defsort S tsig = tsig |> change_tsig (fn (classes, _, types, arities) =>
  (classes, cert_sort tsig S handle TYPE (msg, _, _) => error msg, types, arities));


(* types *)

local

fun err_neg_args c =
  error ("Negative number of arguments in type constructor declaration: " ^ quote c);

fun err_in_decls c decl decl' =
  let
    val s = str_of_decl decl;
    val s' = str_of_decl decl';
  in
    if s = s' then error ("Duplicate declaration of " ^ s ^ ": " ^ quote c)
    else error ("Conflicting declarations of " ^ s ^ " with " ^ s' ^ ": " ^ quote c)
  end;

fun new_decl (c, decl) types =
  (case Symtab.lookup (types, c) of
    Some (decl', _) => err_in_decls c decl decl'
  | None => Symtab.update ((c, (decl, stamp ())), types));

fun the_decl types c = fst (the (Symtab.lookup (types, c)));

fun change_types f = change_tsig (fn (classes, default, types, arities) =>
  (classes, default, f types, arities));

fun add_abbr (a, vs, rhs) tsig = tsig |> change_types (fn types =>
  let
    fun err msg =
      error (msg ^ "\nThe error(s) above occurred in type abbreviation " ^ quote a);
    val rhs' = strip_sorts (varifyT (no_tvars (cert_typ_syntax tsig rhs)))
      handle TYPE (msg, _, _) => err msg;
  in
    (case duplicates vs of
      [] => []
    | dups => err ("Duplicate variables on lhs: " ^ commas_quote dups));
    (case gen_rems (op =) (map (#1 o #1) (typ_tvars rhs'), vs) of
      [] => []
    | extras => err ("Extra variables on rhs: " ^ commas_quote extras));
    types |> new_decl (a, Abbreviation (vs, rhs'))
  end);

in

fun add_types ps = change_types (fold new_decl (ps |> map (fn (c, n) =>
  if n < 0 then err_neg_args c else (c, LogicalType n))));

val add_abbrs = fold add_abbr;
val add_nonterminals = change_types o fold new_decl o map (rpair Nonterminal);

fun merge_types (types1, types2) =
  Symtab.merge Library.eq_snd (types1, types2) handle Symtab.DUPS (d :: _) =>
    err_in_decls d (the_decl types1 d) (the_decl types2 d);

end;


(* merge type signatures *)

fun merge_tsigs (tsig1, tsig2) =
  let
    val (TSig {classes = classes1, default = default1, types = types1, arities = arities1,
      log_types = _, witness = _}) = tsig1;
    val (TSig {classes = classes2, default = default2, types = types2, arities = arities2,
      log_types = _, witness = _}) = tsig2;

    val classes' = merge_classes (classes1, classes2);
    val default' = Sorts.inter_sort classes' (default1, default2);
    val types' = merge_types (types1, types2);
    val arities' = merge_arities classes' (arities1, arities2);
  in build_tsig (classes', default', types', arities') end;

end;
