(*  Title:      Pure/type.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Lawrence C Paulson

Type signatures, unification of types, interface to type inference.
*)

signature TYPE =
sig
  (*TFrees and TVars*)
  val no_tvars: typ -> typ
  val varifyT: typ -> typ
  val unvarifyT: typ -> typ
  val varify: term * string list -> term * (string * indexname) list
  val freeze_thaw_type : typ -> typ * (typ -> typ)
  val freeze_thaw : term -> term * (term -> term)

  (*type signatures*)
  type type_sig
  val rep_tsig: type_sig ->
    {classes: class list,
     classrel: Sorts.classrel,
     default: sort,
     tycons: int Symtab.table,
     log_types: string list,
     univ_witness: (typ * sort) option,
     abbrs: (string list * typ) Symtab.table,
     arities: Sorts.arities}
  val classes: type_sig -> class list
  val defaultS: type_sig -> sort
  val logical_types: type_sig -> string list
  val univ_witness: type_sig -> (typ * sort) option
  val subsort: type_sig -> sort * sort -> bool
  val eq_sort: type_sig -> sort * sort -> bool
  val norm_sort: type_sig -> sort -> sort
  val cert_class: type_sig -> class -> class
  val cert_sort: type_sig -> sort -> sort
  val witness_sorts: type_sig -> sort list -> sort list -> (typ * sort) list
  val rem_sorts: typ -> typ
  val tsig0: type_sig
  val ext_tsig_classes: type_sig -> (class * class list) list -> type_sig
  val ext_tsig_classrel: type_sig -> (class * class) list -> type_sig
  val ext_tsig_defsort: type_sig -> sort -> type_sig
  val ext_tsig_types: type_sig -> (string * int) list -> type_sig
  val ext_tsig_abbrs: type_sig -> (string * string list * typ) list -> type_sig
  val ext_tsig_arities: type_sig -> (string * sort list * sort)list -> type_sig
  val merge_tsigs: type_sig * type_sig -> type_sig
  val typ_errors: type_sig -> typ * string list -> string list
  val cert_typ: type_sig -> typ -> typ
  val cert_typ_no_norm: type_sig -> typ -> typ
  val norm_typ: type_sig -> typ -> typ
  val norm_term: type_sig -> term -> term
  val inst_term_tvars: type_sig * (indexname * typ) list -> term -> term
  val inst_typ_tvars: type_sig * (indexname * typ) list -> typ -> typ

  (*type matching*)
  exception TYPE_MATCH
  val typ_match: type_sig -> typ Vartab.table * (typ * typ)
    -> typ Vartab.table
  val typ_instance: type_sig * typ * typ -> bool
  val of_sort: type_sig -> typ * sort -> bool

  (*type unification*)
  exception TUNIFY
  val unify: type_sig -> typ Vartab.table * int -> typ * typ -> typ Vartab.table * int
  val raw_unify: typ * typ -> bool

  (*type inference*)
  val get_sort: type_sig -> (indexname -> sort option) -> (sort -> sort)
    -> (indexname * sort) list -> indexname -> sort
  val constrain: term -> typ -> term
  val param: int -> string * sort -> typ
  val paramify_dummies: int * typ -> int * typ
  val infer_types: (term -> Pretty.T) -> (typ -> Pretty.T)
    -> type_sig -> (string -> typ option) -> (indexname -> typ option)
    -> (indexname -> sort option) -> (string -> string) -> (typ -> typ)
    -> (sort -> sort) -> string list -> bool -> typ list -> term list
    -> term list * (indexname * typ) list
end;

structure Type: TYPE =
struct


(*** TFrees and TVars ***)

fun no_tvars T =
  (case typ_tvars T of [] => T
  | vs => raise TYPE ("Illegal schematic type variable(s): " ^
      commas (map (Syntax.string_of_vname o #1) vs), [T], []));


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



(*** type signatures ***)

(* type type_sig *)

(*
  classes: list of all declared classes;
  classrel: (see Pure/sorts.ML)
  default: default sort attached to all unconstrained type vars;
  tycons: table of all declared types with the number of their arguments;
  log_types: list of logical type constructors sorted by number of arguments;
  univ_witness: type witnessing non-emptiness of least sort
  abbrs: table of type abbreviations;
  arities: (see Pure/sorts.ML)
*)

datatype type_sig =
  TySg of {
    classes: class list,
    classrel: Sorts.classrel,
    default: sort,
    tycons: int Symtab.table,
    log_types: string list,
    univ_witness: (typ * sort) option,
    abbrs: (string list * typ) Symtab.table,
    arities: Sorts.arities};

fun rep_tsig (TySg comps) = comps;

fun classes (TySg {classes = cs, ...}) = cs;
fun defaultS (TySg {default, ...}) = default;
fun logical_types (TySg {log_types, ...}) = log_types;
fun univ_witness (TySg {univ_witness, ...}) = univ_witness;


(* error messages *)

fun undeclared_class c = "Undeclared class: " ^ quote c;
fun undeclared_classes cs = "Undeclared class(es): " ^ commas_quote cs;

fun err_undeclared_class s = error (undeclared_class s);

fun err_dup_classes cs =
  error ("Duplicate declaration of class(es): " ^ commas_quote cs);

fun undeclared_type c = "Undeclared type constructor: " ^ quote c;

fun err_neg_args c =
  error ("Negative number of arguments of type constructor: " ^ quote c);

fun err_dup_tycon c =
  error ("Duplicate declaration of type constructor: " ^ quote c);

fun dup_tyabbrs ts =
  "Duplicate declaration of type abbreviation(s): " ^ commas_quote ts;

fun ty_confl c = "Conflicting type constructor and abbreviation: " ^ quote c;


(* sorts *)

fun subsort (TySg {classrel, ...}) = Sorts.sort_le classrel;
fun eq_sort (TySg {classrel, ...}) = Sorts.sort_eq classrel;
fun norm_sort (TySg {classrel, ...}) = Sorts.norm_sort classrel;

fun cert_class (TySg {classes, ...}) c =
  if c mem_string classes then c else raise TYPE (undeclared_class c, [], []);

fun cert_sort tsig S = norm_sort tsig (map (cert_class tsig) S);

fun witness_sorts (tsig as TySg {classrel, arities, log_types, ...}) =
  Sorts.witness_sorts (classrel, arities, log_types);

fun rem_sorts (Type (a, tys)) = Type (a, map rem_sorts tys)
  | rem_sorts (TFree (x, _)) = TFree (x, [])
  | rem_sorts (TVar (xi, _)) = TVar (xi, []);


(* FIXME err_undeclared_class! *)
(* 'leq' checks the partial order on classes according to the
   statements in classrel 'a'
*)

fun less a (C, D) = case Symtab.lookup (a, C) of
     Some ss => D mem_string ss
   | None => err_undeclared_class C;

fun leq a (C, D)  =  C = D orelse less a (C, D);



(* FIXME *)
(*Instantiation of type variables in types*)
(*Pre: instantiations obey restrictions! *)
fun inst_typ tye =
  let fun inst(var as (v, _)) = case assoc(tye, v) of
                                  Some U => inst_typ tye U
                                | None => TVar(var)
  in map_type_tvar inst end;



fun of_sort (TySg {classrel, arities, ...}) = Sorts.of_sort (classrel, arities);

fun check_has_sort (tsig, T, S) =
  if of_sort tsig (T, S) then ()
  else raise TYPE ("Type not of sort " ^ Sorts.str_of_sort S, [T], []);


(*Instantiation of type variables in types *)
fun inst_typ_tvars(tsig, tye) =
  let fun inst(var as (v, S)) = case assoc(tye, v) of
              Some U => (check_has_sort(tsig, U, S); U)
            | None => TVar(var)
  in map_type_tvar inst end;

(*Instantiation of type variables in terms *)
fun inst_term_tvars (_,[]) t = t
  | inst_term_tvars arg    t = map_term_types (inst_typ_tvars arg) t;


(* norm_typ, norm_term *)

(*expand abbreviations and normalize sorts*)
fun norm_typ (tsig as TySg {abbrs, ...}) ty =
  let
    val idx = maxidx_of_typ ty + 1;

    fun norm (Type (a, Ts)) =
          (case Symtab.lookup (abbrs, a) of
            Some (vs, U) => norm (inst_typ (map (rpair idx) vs ~~ Ts) (incr_tvar idx U))
          | None => Type (a, map norm Ts))
      | norm (TFree (x, S)) = TFree (x, norm_sort tsig S)
      | norm (TVar (xi, S)) = TVar (xi, norm_sort tsig S);

    val ty' = norm ty;
  in if ty = ty' then ty else ty' end;  (*dumb tuning to avoid copying*)

fun norm_term tsig t =
  let val t' = map_term_types (norm_typ tsig) t
  in if t = t' then t else t' end;  (*dumb tuning to avoid copying*)



(** build type signatures **)

fun make_tsig (classes, classrel, default, tycons, log_types, univ_witness, abbrs, arities) =
  TySg {classes = classes, classrel = classrel, default = default, tycons = tycons,
    log_types = log_types, univ_witness = univ_witness, abbrs = abbrs, arities = arities};

fun rebuild_tsig (TySg {classes, classrel, default, tycons, log_types = _, univ_witness = _, abbrs, arities}) =
  let
    fun log_class c = Sorts.class_le classrel (c, logicC);
    fun log_type (t, _) = exists (log_class o #1) (Symtab.lookup_multi (arities, t));
    val ts = filter log_type (Symtab.dest tycons);

    val log_types = map #1 (Library.sort (Library.int_ord o pairself #2) ts);
    val univ_witness =
      (case Sorts.witness_sorts (classrel, arities, log_types) [] [classes] of
        [w] => Some w | _ => None);
  in make_tsig (classes, classrel, default, tycons, log_types, univ_witness, abbrs, arities) end;

val tsig0 =
  make_tsig ([], Symtab.empty, [], Symtab.empty, [], None, Symtab.empty, Symtab.empty)
  |> rebuild_tsig;


(* typ_errors *)

(*check validity of (not necessarily normal) type; accumulate error messages*)

fun typ_errors tsig (typ, errors) =
  let
    val {classes, tycons, abbrs, ...} = rep_tsig tsig;

    fun class_err (errs, c) =
      if c mem_string classes then errs
      else undeclared_class c ins_string errs;

    val sort_err = foldl class_err;

    fun typ_errs (errs, Type (c, Us)) =
          let
            val errs' = foldl typ_errs (errs, Us);
            fun nargs n =
              if n = length Us then errs'
              else ("Wrong number of arguments: " ^ quote c) ins_string errs';
          in
            (case Symtab.lookup (tycons, c) of
              Some n => nargs n
            | None =>
                (case Symtab.lookup (abbrs, c) of
                  Some (vs, _) => nargs (length vs)
                | None => undeclared_type c ins_string errs))
          end
    | typ_errs (errs, TFree (_, S)) = sort_err (errs, S)
    | typ_errs (errs, TVar ((x, i), S)) =
        if i < 0 then
          ("Negative index for TVar " ^ quote x) ins_string sort_err (errs, S)
        else sort_err (errs, S);
  in typ_errs (errors, typ) end;


(* cert_typ *)           (*exception TYPE*)

fun cert_typ_no_norm tsig T =
  (case typ_errors tsig (T, []) of
    [] => T
  | errs => raise TYPE (cat_lines errs, [T], []));

fun cert_typ tsig T = norm_typ tsig (cert_typ_no_norm tsig T);



(** merge type signatures **)

(* merge classrel *)

fun assoc_union (as1, []) = as1
  | assoc_union (as1, (key, l2) :: as2) =
      (case assoc_string (as1, key) of
        Some l1 => assoc_union (overwrite (as1, (key, l1 union_string l2)), as2)
      | None => assoc_union ((key, l2) :: as1, as2));

fun merge_classrel (classrel1, classrel2) =
  let
    val classrel = transitive_closure (assoc_union (Symtab.dest classrel1, Symtab.dest classrel2))
  in
    if exists (op mem_string) classrel then
      error ("Cyclic class structure!")   (* FIXME improve msg, raise TERM *)
    else Symtab.make classrel
  end;


(* coregularity *)

local

(* 'is_unique_decl' checks if there exists just one declaration t:(Ss)C *)

fun is_unique_decl ars (t,(C,w)) = case assoc (ars, C) of
      Some(w1) => if w = w1 then () else
        error("There are two declarations\n" ^
              Sorts.str_of_arity(t, w, [C]) ^ " and\n" ^
              Sorts.str_of_arity(t, w1, [C]) ^ "\n" ^
              "with the same result class.")
    | None => ();

(* 'coreg' checks if there are two declarations t:(Ss1)C1 and t:(Ss2)C2
   such that C1 >= C2 then Ss1 >= Ss2 (elementwise) *)

fun coreg_err(t, (C1,w1), (C2,w2)) =
    error("Declarations " ^ Sorts.str_of_arity(t, w1, [C1]) ^ " and "
                          ^ Sorts.str_of_arity(t, w2, [C2]) ^ " are in conflict");

fun coreg classrel (t, Cw1) =
  let
    fun check1(Cw1 as (C1,w1), Cw2 as (C2,w2)) =
      if leq classrel (C1,C2) then
        if Sorts.sorts_le classrel (w1,w2) then ()
        else coreg_err(t, Cw1, Cw2)
      else ()
    fun check(Cw2) = (check1(Cw1,Cw2); check1(Cw2,Cw1))
  in seq check end;

in

fun add_arity classrel ars (tCw as (_,Cw)) =
      (is_unique_decl ars tCw; coreg classrel tCw ars; Cw ins ars);

end;


(* 'merge_arities' builds the union of two 'arities' lists;
   it only checks the two restriction conditions and inserts afterwards
   all elements of the second list into the first one *)

local

fun merge_arities_aux classrel =
  let fun test_ar t (ars1, sw) = add_arity classrel ars1 (t,sw);

      fun merge_c (arities1, (c as (t, ars2))) = case assoc (arities1, t) of
          Some(ars1) =>
            let val ars = foldl (test_ar t) (ars1, ars2)
            in overwrite (arities1, (t,ars)) end
        | None => c::arities1
  in foldl merge_c end;

in

fun merge_arities classrel (a1, a2) =
  Symtab.make (merge_arities_aux classrel (Symtab.dest a1, Symtab.dest a2));

end;


(* tycons *)

fun varying_decls t =
  error ("Type constructor " ^ quote t ^ " has varying number of arguments");

fun add_tycons (tycons, tn as (t,n)) =
  (case Symtab.lookup (tycons, t) of
    Some m => if m = n then tycons else varying_decls t
  | None => Symtab.update (tn, tycons));


(* merge_abbrs *)

fun merge_abbrs abbrs =
  Symtab.merge (op =) abbrs handle Symtab.DUPS dups => raise TERM (dup_tyabbrs dups, []);


(* merge_tsigs *)

fun merge_tsigs
 (TySg {classes = classes1, default = default1, classrel = classrel1, tycons = tycons1,
    log_types = _, univ_witness = _, arities = arities1, abbrs = abbrs1},
  TySg {classes = classes2, default = default2, classrel = classrel2, tycons = tycons2,
    log_types = _, univ_witness = _, arities = arities2, abbrs = abbrs2}) =
  let
    val classes' = classes1 union_string classes2;
    val classrel' = merge_classrel (classrel1, classrel2);
    val arities' = merge_arities classrel' (arities1, arities2);
    val tycons' = foldl add_tycons (tycons1, Symtab.dest tycons2);
    val default' = Sorts.norm_sort classrel' (default1 @ default2);
    val abbrs' = merge_abbrs (abbrs1, abbrs2);
  in
    make_tsig (classes', classrel', default', tycons', [], None, abbrs', arities')
    |> rebuild_tsig
  end;



(*** extend type signatures ***)

(** add classes and classrel relations **)

fun add_classes classes cs =
  (case cs inter_string classes of
    [] => cs @ classes
  | dups => err_dup_classes cs);


(*'add_classrel' adds a tuple consisting of a new class (the new class has
  already been inserted into the 'classes' list) and its superclasses (they
  must be declared in 'classes' too) to the 'classrel' list of the given type
  signature; furthermore all inherited superclasses according to the
  superclasses brought with are inserted and there is a check that there are
  no cycles (i.e. C <= D <= C, with C <> D);*)

fun add_classrel classes (classrel, (s, ges)) =
  let
    fun upd (classrel, s') =
      if s' mem_string classes then
        let val ges' = the (Symtab.lookup (classrel, s))
        in case Symtab.lookup (classrel, s') of
             Some sups => if s mem_string sups
                           then error(" Cycle :" ^ s^" <= "^ s'^" <= "^ s )
                           else Symtab.update ((s, sups union_string ges'), classrel)
           | None => classrel
        end
      else err_undeclared_class s'
  in foldl upd (Symtab.update ((s, ges), classrel), ges) end;


(* 'extend_classes' inserts all new classes into the corresponding
   lists ('classes', 'classrel') if possible *)

fun extend_classes (classes, classrel, new_classes) =
  let
    val classes' = add_classes classes (map fst new_classes);
    val classrel' = foldl (add_classrel classes') (classrel, new_classes);
  in (classes', classrel') end;


(* ext_tsig_classes *)

fun ext_tsig_classes tsig new_classes =
  let
    val TySg {classes, classrel, default, tycons, log_types, univ_witness, abbrs, arities} = tsig;
    val (classes', classrel') = extend_classes (classes,classrel, new_classes);
  in
    make_tsig (classes', classrel', default, tycons, log_types, univ_witness, abbrs, arities)
    |> rebuild_tsig
  end;


(* ext_tsig_classrel *)

fun ext_tsig_classrel tsig pairs =
  let
    val TySg {classes, classrel, default, tycons, log_types, univ_witness, abbrs, arities} = tsig;
    val cert = cert_class tsig;

    (* FIXME clean! *)
    val classrel' =
      merge_classrel (classrel, Symtab.make (map (fn (c1, c2) => (cert c1, [cert c2])) pairs));
  in
    make_tsig (classes, classrel', default, tycons, log_types, univ_witness, abbrs, arities)
    |> rebuild_tsig
  end;


(* ext_tsig_defsort *)

fun ext_tsig_defsort
    (TySg {classes, classrel, default = _, tycons, log_types, univ_witness, abbrs, arities, ...}) default =
  make_tsig (classes, classrel, default, tycons, log_types, univ_witness, abbrs, arities);



(** add types **)

fun ext_tsig_types (TySg {classes, classrel, default, tycons, log_types, univ_witness, abbrs, arities}) ts =
  let
    fun check_type (c, n) =
      if n < 0 then err_neg_args c
      else if is_some (Symtab.lookup (tycons, c)) then err_dup_tycon c
      else if is_some (Symtab.lookup (abbrs, c)) then error (ty_confl c)
      else ();
    val _ = seq check_type ts;
    val tycons' = Symtab.extend (tycons, ts);
    val arities' = Symtab.extend (arities, map (rpair [] o #1) ts);
  in make_tsig (classes, classrel, default, tycons', log_types, univ_witness, abbrs, arities') end;



(** add type abbreviations **)

fun abbr_errors tsig (a, (lhs_vs, rhs)) =
  let
    val TySg {tycons, abbrs, ...} = tsig;
    val rhs_vs = map (#1 o #1) (typ_tvars rhs);

    val dup_lhs_vars =
      (case duplicates lhs_vs of
        [] => []
      | vs => ["Duplicate variables on lhs: " ^ commas_quote vs]);

    val extra_rhs_vars =
      (case gen_rems (op =) (rhs_vs, lhs_vs) of
        [] => []
      | vs => ["Extra variables on rhs: " ^ commas_quote vs]);

    val tycon_confl =
      if is_none (Symtab.lookup (tycons, a)) then []
      else [ty_confl a];

    val dup_abbr =
      if is_none (Symtab.lookup (abbrs, a)) then []
      else ["Duplicate declaration of abbreviation"];
  in
    dup_lhs_vars @ extra_rhs_vars @ tycon_confl @ dup_abbr @
      typ_errors tsig (rhs, [])
  end;

fun prep_abbr tsig (a, vs, raw_rhs) =
  let
    fun err msgs = (seq error_msg msgs;
      error ("The error(s) above occurred in type abbreviation " ^ quote a));

    val rhs = rem_sorts (varifyT (no_tvars raw_rhs))
      handle TYPE (msg, _, _) => err [msg];
    val abbr = (a, (vs, rhs));
  in
    (case abbr_errors tsig abbr of
      [] => abbr
    | msgs => err msgs)
  end;

fun add_abbr
    (tsig as TySg {classes, classrel, default, tycons, log_types, univ_witness, arities, abbrs}, abbr) =
  make_tsig (classes, classrel, default, tycons, log_types, univ_witness,
    Symtab.update (prep_abbr tsig abbr, abbrs), arities);

fun ext_tsig_abbrs tsig raw_abbrs = foldl add_abbr (tsig, raw_abbrs);



(** add arities **)

(* 'coregular' checks
   - the two restrictions 'is_unique_decl' and 'coreg'
   - if the classes in the new type declarations are known in the
     given type signature
   - if one type constructor has always the same number of arguments;
   if one type declaration has passed all checks it is inserted into
   the 'arities' association list of the given type signatrure  *)

fun coregular (classes, classrel, tycons) =
  let fun ex C = if C mem_string classes then () else err_undeclared_class(C);

      fun addar(arities, (t, (w, C))) = case Symtab.lookup (tycons, t) of
            Some(n) => if n <> length w then varying_decls(t) else
                     ((seq o seq) ex w; ex C;
                      let val ars = the (Symtab.lookup (arities, t))
                          val ars' = add_arity classrel ars (t,(C,w))
                      in Symtab.update ((t,ars'), arities) end)
          | None => error (undeclared_type t);

  in addar end;


(* 'close' extends the 'arities' association list after all new type
   declarations have been inserted successfully:
   for every declaration t:(Ss)C , for all classses D with C <= D:
      if there is no declaration t:(Ss')C' with C < C' and C' <= D
      then insert the declaration t:(Ss)D into 'arities'
   this means, if there exists a declaration t:(Ss)C and there is
   no declaration t:(Ss')D with C <=D then the declaration holds
   for all range classes more general than C *)

fun close classrel arities =
  let fun check sl (l, (s, dom)) = case Symtab.lookup (classrel, s) of
          Some sups =>
            let fun close_sup (l, sup) =
                  if exists (fn s'' => less classrel (s, s'') andalso
                                       leq classrel (s'', sup)) sl
                  then l
                  else (sup, dom)::l
            in foldl close_sup (l, sups) end
        | None => l;
      fun ext (s, l) = (s, foldl (check (map #1 l)) (l, l));
  in map ext arities end;


(* ext_tsig_arities *)

fun norm_domain classrel =
  let fun one_min (f, (doms, ran)) = (f, (map (Sorts.norm_sort classrel) doms, ran))
  in map one_min end;

fun ext_tsig_arities tsig sarities =
  let
    val TySg {classes, classrel, default, tycons, log_types, univ_witness, arities, abbrs} = tsig;
    val arities1 =
      flat (map (fn (t, ss, cs) => map (fn c => (t, (ss, c))) cs) sarities);
    val arities2 =
      foldl (coregular (classes, classrel, tycons)) (arities, norm_domain classrel arities1)
      |> Symtab.dest |> close classrel |> Symtab.make;
  in
    make_tsig (classes, classrel, default, tycons, log_types, univ_witness, abbrs, arities2)
    |> rebuild_tsig
  end;



(*** type unification and friends ***)

(** matching **)

exception TYPE_MATCH;

fun typ_match tsig =
  let
    fun match (subs, (TVar (v, S), T)) =
          (case Vartab.lookup (subs, v) of
            None => (Vartab.update_new ((v, (check_has_sort (tsig, T, S); T)), subs)
              handle TYPE _ => raise TYPE_MATCH)
          | Some U => if U = T then subs else raise TYPE_MATCH)
      | match (subs, (Type (a, Ts), Type (b, Us))) =
          if a <> b then raise TYPE_MATCH
          else foldl match (subs, Ts ~~ Us)
      | match (subs, (TFree x, TFree y)) =
          if x = y then subs else raise TYPE_MATCH
      | match _ = raise TYPE_MATCH;
  in match end;

fun typ_instance (tsig, T, U) =
  (typ_match tsig (Vartab.empty, (U, T)); true) handle TYPE_MATCH => false;



(** unification **)

exception TUNIFY;


(* occurs check *)

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


(* chase variable assignments *)

(*if devar returns a type var then it must be unassigned*)
fun devar (T as TVar (v, _), tye) =
      (case  Vartab.lookup (tye, v) of
        Some U => devar (U, tye)
      | None => T)
  | devar (T, tye) = T;


(* add_env *)

(*avoids chains 'a |-> 'b |-> 'c ...*)
fun add_env (vT as (v, T), tab) = Vartab.update_new (vT, Vartab.map
  (fn (U as (TVar (w, S))) => if eq_ix (v, w) then T else U | U => U) tab);


(* unify *)

fun unify (tsig as TySg {classrel, arities, ...}) (tyenv, maxidx) TU =
  let
    val tyvar_count = ref maxidx;
    fun gen_tyvar S = TVar (("'a", inc tyvar_count), S);

    fun mg_domain a S =
      Sorts.mg_domain (classrel, arities) a S handle Sorts.DOMAIN _ => raise TUNIFY;

    fun meet ((_, []), tye) = tye
      | meet ((TVar (xi, S'), S), tye) =
          if Sorts.sort_le classrel (S', S) then tye
          else add_env ((xi, gen_tyvar (Sorts.inter_sort classrel (S', S))), tye)
      | meet ((TFree (_, S'), S), tye) =
          if Sorts.sort_le classrel (S', S) then tye
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
          else if Sorts.sort_le classrel (S1, S2) then add_env ((w, T), tye)
          else if Sorts.sort_le classrel (S2, S1) then add_env ((v, U), tye)
          else
            let val S = gen_tyvar (Sorts.inter_sort classrel (S1, S2)) in
              add_env ((v, S), add_env ((w, S), tye))
            end
      | (TVar (v, S), T) =>
          if occurs v tye T then raise TUNIFY
          else meet ((T, S), add_env ((v, T), tye))
      | (T, TVar (v, S)) =>
          if occurs v tye T then raise TUNIFY
          else meet ((T, S), add_env ((v, T), tye))
      | (Type (a, Ts), Type (b, Us)) =>
          if a <> b then raise TUNIFY
          else foldr unif (Ts ~~ Us, tye)
      | (T, U) => if T = U then tye else raise TUNIFY);
  in (unif (TU, tyenv), ! tyvar_count) end;


(* raw_unify *)

(*purely structural unification -- ignores sorts*)
fun raw_unify (ty1, ty2) =
  (unify tsig0 (Vartab.empty, 0) (rem_sorts ty1, rem_sorts ty2); true)
    handle TUNIFY => false;



(** type inference **)

(* sort constraints *)

fun get_sort tsig def_sort map_sort raw_env =
  let
    fun eq ((xi, S), (xi', S')) =
      xi = xi' andalso eq_sort tsig (S, S');

    val env = gen_distinct eq (map (apsnd map_sort) raw_env);
    val _ =
      (case gen_duplicates eq_fst env of
        [] => ()
      | dups => error ("Inconsistent sort constraints for type variable(s) " ^
          commas (map (quote o Syntax.string_of_vname' o fst) dups)));

    fun get xi =
      (case (assoc (env, xi), def_sort xi) of
        (None, None) => defaultS tsig
      | (None, Some S) => S
      | (Some S, None) => S
      | (Some S, Some S') =>
          if eq_sort tsig (S, S') then S'
          else error ("Sort constraint inconsistent with default for type variable " ^
            quote (Syntax.string_of_vname' xi)));
  in get end;


(* type constraints *)

fun constrain t T =
  if T = dummyT then t
  else Const ("_type_constraint_", T) $ t;


(* user parameters *)

fun is_param (x, _) = size x > 0 andalso ord x = ord "?";
fun param i (x, S) = TVar (("?" ^ x, i), S);

fun paramify_dummies (i, TFree ("'_dummy_", S)) = (i + 1, param i ("'dummy", S))
  | paramify_dummies (i, Type (a, Ts)) =
      let val (i', Ts') = foldl_map paramify_dummies (i, Ts)
      in (i', Type (a, Ts')) end
  | paramify_dummies arg = arg;


(* decode_types *)

(*transform parse tree into raw term*)
fun decode_types tsig is_const def_type def_sort map_const map_type map_sort tm =
  let
    fun get_type xi = if_none (def_type xi) dummyT;
    fun is_free x = is_some (def_type (x, ~1));
    val raw_env = Syntax.raw_term_sorts tm;
    val sort_of = get_sort tsig def_sort map_sort raw_env;

    val certT = cert_typ tsig o map_type;
    fun decodeT t = certT (Syntax.typ_of_term sort_of map_sort t);

    fun decode (Const ("_constrain", _) $ t $ typ) =
          constrain (decode t) (decodeT typ)
      | decode (Const ("_constrainAbs", _) $ (Abs (x, T, t)) $ typ) =
          if T = dummyT then Abs (x, decodeT typ, decode t)
          else constrain (Abs (x, certT T, decode t)) (decodeT typ --> dummyT)
      | decode (Abs (x, T, t)) = Abs (x, certT T, decode t)
      | decode (t $ u) = decode t $ decode u
      | decode (Free (x, T)) =
          let val c = map_const x in
            if not (is_free x) andalso (is_const c orelse NameSpace.is_qualified c) then
              Const (c, certT T)
            else if T = dummyT then Free (x, get_type (x, ~1))
            else constrain (Free (x, certT T)) (get_type (x, ~1))
          end
      | decode (Var (xi, T)) =
          if T = dummyT then Var (xi, get_type xi)
          else constrain (Var (xi, certT T)) (get_type xi)
      | decode (t as Bound _) = t
      | decode (Const (c, T)) = Const (map_const c, certT T);
  in decode tm end;


(* infer_types *)

(*
  Given [T1,...,Tn] and [t1,...,tn], ensure that the type of ti
  unifies with Ti (for i=1,...,n).

  tsig: type signature
  const_type: name mapping and signature lookup
  def_type: partial map from indexnames to types (constrains Frees, Vars)
  def_sort: partial map from indexnames to sorts (constrains TFrees, TVars)
  used: list of already used type variables
  freeze: if true then generated parameters are turned into TFrees, else TVars
*)

fun infer_types prt prT tsig const_type def_type def_sort
    map_const map_type map_sort used freeze pat_Ts raw_ts =
  let
    val TySg {classrel, arities, ...} = tsig;
    val pat_Ts' = map (cert_typ tsig) pat_Ts;
    val is_const = is_some o const_type;
    val raw_ts' =
      map (decode_types tsig is_const def_type def_sort map_const map_type map_sort) raw_ts;
    val (ts, Ts, unifier) =
      TypeInfer.infer_types prt prT const_type classrel arities used freeze
        is_param raw_ts' pat_Ts';
  in (ts, unifier) end;


end;
