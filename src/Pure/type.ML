(*  Title:      Pure/type.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Lawrence C Paulson

Type classes and sorts. Type signatures. Type unification and inference.

TODO:
  improve nonempty_sort!
  move type unification and inference to type_unify.ML (TypeUnify) (?)
*)

signature TYPE =
  sig
  exception TUNIFY
  exception TYPE_MATCH
  val no_tvars: typ -> typ
  val varifyT: typ -> typ
  val unvarifyT: typ -> typ
  val varify: term * string list -> term
  val str_of_sort: sort -> string
  val str_of_arity: string * sort list * sort -> string
  type type_sig
  val rep_tsig: type_sig ->
    {classes: class list,
     subclass: (class * class list) list,
     default: sort,
     tycons: (string * int) list,
     abbrs: (string * (string list * typ)) list,
     arities: (string * (class * sort list) list) list}
  val defaultS: type_sig -> sort
  val tsig0: type_sig
  val logical_types: type_sig -> string list
  val ext_tsig_classes: type_sig -> (class * class list) list -> type_sig
  val ext_tsig_subclass: type_sig -> (class * class) list -> type_sig
  val ext_tsig_defsort: type_sig -> sort -> type_sig
  val ext_tsig_types: type_sig -> (string * int) list -> type_sig
  val ext_tsig_abbrs: type_sig -> (string * string list * typ) list -> type_sig
  val ext_tsig_arities: type_sig -> (string * sort list * sort)list -> type_sig
  val merge_tsigs: type_sig * type_sig -> type_sig
  val subsort: type_sig -> sort * sort -> bool
  val norm_sort: type_sig -> sort -> sort
  val rem_sorts: typ -> typ
  val nonempty_sort: type_sig -> sort list -> sort -> bool
  val cert_typ: type_sig -> typ -> typ
  val norm_typ: type_sig -> typ -> typ
  val freeze: term -> term
  val freeze_vars: typ -> typ
  val infer_types: type_sig * (string -> typ option) *
                   (indexname -> typ option) * (indexname -> sort option) *
                   string list * bool * typ list * term list
                   -> term list * (indexname * typ) list
  val inst_term_tvars: type_sig * (indexname * typ) list -> term -> term
  val thaw_vars: typ -> typ
  val typ_errors: type_sig -> typ * string list -> string list
  val typ_instance: type_sig * typ * typ -> bool
  val typ_match: type_sig -> (indexname * typ) list * (typ * typ)
    -> (indexname * typ) list
  val unify: type_sig -> int -> (indexname * typ) list -> (typ * typ)
    -> (indexname * typ) list * int
  val raw_unify: typ * typ -> bool
  end;

structure Type : TYPE =
struct

(*** TFrees vs TVars ***)

(*disallow TVars*)
fun no_tvars T =
  if null (typ_tvars T) then T
  else raise_type "Illegal schematic type variable(s)" [T] [];

(*turn TFrees into TVars to allow types & axioms to be written without "?"*)
val varifyT = map_type_tfree (fn (a, S) => TVar((a, 0), S));

(*inverse of varifyT*)
fun unvarifyT (Type (a, Ts)) = Type (a, map unvarifyT Ts)
  | unvarifyT (TVar ((a, 0), S)) = TFree (a, S)
  | unvarifyT T = T;

(*turn TFrees except those in fixed into new TVars*)
fun varify (t, fixed) =
  let
    val fs = add_term_tfree_names (t, []) \\ fixed;
    val ixns = add_term_tvar_ixns (t, []);
    val fmap = fs ~~ variantlist (fs, map #1 ixns)
    fun thaw(f as (a,S)) = case assoc (fmap, a) of
                             None => TFree(f)
                           | Some b => TVar((b, 0), S)
  in  map_term_types (map_type_tfree thaw) t  end;



(*** type classes and sorts ***)

(*
  Classes denote (possibly empty) collections of types (e.g. sets of types)
  and are partially ordered by 'inclusion'. They are represented by strings.

  Sorts are intersections of finitely many classes. They are represented by
  lists of classes.
*)

type domain = sort list;


(* print sorts and arities *)

fun str_of_sort [c] = c
  | str_of_sort cs = enclose "{" "}" (commas cs);

fun str_of_dom dom = enclose "(" ")" (commas (map str_of_sort dom));

fun str_of_arity (t, [], S) = t ^ " :: " ^ str_of_sort S
  | str_of_arity (t, SS, S) =
      t ^ " :: " ^ str_of_dom SS ^ " " ^ str_of_sort S;



(*** type signatures ***)

(*
  classes:
    a list of all declared classes;

  subclass:
    an association list representing the subclass relation; (c, cs) is
    interpreted as "c is a proper subclass of all elemenst of cs"; note that
    c itself is not a memeber of cs;

  default:
    the default sort attached to all unconstrained type vars;

  tycons:
    an association list of all declared types with the number of their
    arguments;

  abbrs:
    an association list of type abbreviations;

  arities:
    a two-fold association list of all type arities; (t, al) means that type
    constructor t has the arities in al; an element (c, ss) of al represents
    the arity (ss)c;
*)

datatype type_sig =
  TySg of {
    classes: class list,
    subclass: (class * class list) list,
    default: sort,
    tycons: (string * int) list,
    abbrs: (string * (string list * typ)) list,
    arities: (string * (class * domain) list) list};

fun rep_tsig (TySg comps) = comps;

fun defaultS (TySg {default, ...}) = default;


(* error messages *)

fun undcl_class c = "Undeclared class " ^ quote c;
fun err_undcl_class s = error (undcl_class s);

fun err_dup_classes cs =
  error ("Duplicate declaration of class(es) " ^ commas_quote cs);

fun undcl_type c = "Undeclared type constructor " ^ quote c;

fun err_neg_args c =
  error ("Negative number of arguments of type constructor " ^ quote c);

fun err_dup_tycon c =
  error ("Duplicate declaration of type constructor " ^ quote c);

fun dup_tyabbrs ts =
  "Duplicate declaration of type abbreviation(s) " ^ commas_quote ts;

fun ty_confl c = "Conflicting type constructor and abbreviation " ^ quote c;


(* 'leq' checks the partial order on classes according to the
   statements in the association list 'a' (i.e. 'subclass')
*)

fun less a (C, D) = case assoc (a, C) of
     Some ss => D mem_string ss
   | None => err_undcl_class C;

fun leq a (C, D)  =  C = D orelse less a (C, D);


(* logical_types *)

(*return all logical types of tsig, i.e. all types t with some arity t::(ss)c
  and c <= logic*)

fun logical_types tsig =
  let
    val TySg {subclass, arities, tycons, ...} = tsig;

    fun log_class c = leq subclass (c, logicC);
    fun log_type t = exists (log_class o #1) (assocs arities t);
  in
    filter log_type (map #1 tycons)
  end;


(* 'sortorder' checks the ordering on sets of classes, i.e. on sorts:
   S1 <= S2 , iff for every class C2 in S2 there exists a class C1 in S1
   with C1 <= C2 (according to an association list 'a')
*)

fun sortorder a (S1, S2) =
  forall  (fn C2 => exists  (fn C1 => leq a (C1, C2))  S1)  S2;


(* 'inj' inserts a new class C into a given class set S (i.e.sort) only if
  there exists no class in S which is <= C;
  the resulting set is minimal if S was minimal
*)

fun inj a (C, S) =
  let fun inj1 [] = [C]
        | inj1 (D::T) = if leq a (D, C) then D::T
                        else if leq a (C, D) then inj1 T
                             else D::(inj1 T)
  in inj1 S end;


(* 'union_sort' forms the minimal union set of two sorts S1 and S2
   under the assumption that S2 is minimal *)
(* FIXME rename to inter_sort (?) *)

fun union_sort a = foldr (inj a);


(* 'elementwise_union' forms elementwise the minimal union set of two
   sort lists under the assumption that the two lists have the same length
*)

fun elementwise_union a (Ss1, Ss2) = map (union_sort a) (Ss1~~Ss2);


(* 'lew' checks for two sort lists the ordering for all corresponding list
   elements (i.e. sorts) *)

fun lew a (w1, w2) = forall (sortorder a)  (w1~~w2);


(* 'is_min' checks if a class C is minimal in a given sort S under the
   assumption that S contains C *)

fun is_min a S C = not (exists (fn (D) => less a (D, C)) S);


(* 'min_sort' reduces a sort to its minimal classes *)

fun min_sort a S = distinct(filter (is_min a S) S);


(* 'min_domain' minimizes the domain sorts of type declarationsl;
   the function will be applied on the type declarations in extensions *)

fun min_domain subclass =
  let fun one_min (f, (doms, ran)) = (f, (map (min_sort subclass) doms, ran))
  in map one_min end;


(* 'min_filter' filters a list 'ars' consisting of arities (domain * class)
   and gives back a list of those range classes whose domains meet the
   predicate 'pred' *)

fun min_filter a pred ars =
  let fun filt ([], l) = l
        | filt ((c, x)::xs, l) = if pred(x) then filt (xs, inj a (c, l))
                               else filt (xs, l)
  in filt (ars, []) end;


(* 'cod_above' filters all arities whose domains are elementwise >= than
   a given domain 'w' and gives back a list of the corresponding range
   classes *)

fun cod_above (a, w, ars) = min_filter a (fn w' => lew a (w, w')) ars;



(*Instantiation of type variables in types*)
(*Pre: instantiations obey restrictions! *)
fun inst_typ tye =
  let fun inst(var as (v, _)) = case assoc(tye, v) of
                                  Some U => inst_typ tye U
                                | None => TVar(var)
  in map_type_tvar inst end;

(* 'least_sort' returns for a given type its maximum sort:
   - type variables, free types: the sort brought with
   - type constructors: recursive determination of the maximum sort of the
                    arguments if the type is declared in 'arities' of the
                    given type signature  *)

fun least_sort (tsig as TySg{subclass, arities, ...}) =
  let fun ls(T as Type(a, Ts)) =
                 (case assoc (arities, a) of
                          Some(ars) => cod_above(subclass, map ls Ts, ars)
                        | None => raise TYPE(undcl_type a, [T], []))
        | ls(TFree(a, S)) = S
        | ls(TVar(a, S)) = S
  in ls end;


fun check_has_sort(tsig as TySg{subclass, arities, ...}, T, S) =
  if sortorder subclass ((least_sort tsig T), S) then ()
  else raise TYPE("Type not of sort " ^ (str_of_sort S), [T], [])


(*Instantiation of type variables in types *)
fun inst_typ_tvars(tsig, tye) =
  let fun inst(var as (v, S)) = case assoc(tye, v) of
              Some U => (check_has_sort(tsig, U, S); U)
            | None => TVar(var)
  in map_type_tvar inst end;

(*Instantiation of type variables in terms *)
fun inst_term_tvars(tsig, tye) = map_term_types (inst_typ_tvars(tsig, tye));


(* norm_typ *)

fun norm_typ (TySg {abbrs, ...}) ty =
  let
    val idx = maxidx_of_typ ty + 1;

    fun expand (Type (a, Ts)) =
          (case assoc (abbrs, a) of
            Some (vs, U) =>
              expand (inst_typ (map (rpair idx) vs ~~ Ts) (incr_tvar idx U))
          | None => Type (a, map expand Ts))
      | expand T = T
  in
    expand ty
  end;


(** type matching **)

exception TYPE_MATCH;

(*typ_match (s, (U, T)) = s' <==> s'(U) = T and s' is an extension of s*)
fun typ_match tsig =
  let
    fun match (subs, (TVar (v, S), T)) =
          (case assoc (subs, v) of
            None => ((v, (check_has_sort (tsig, T, S); T)) :: subs
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
  (typ_match tsig ([], (U, T)); true) handle TYPE_MATCH => false;



(** build type signatures **)

fun make_tsig (classes, subclass, default, tycons, abbrs, arities) =
  TySg {classes = classes, subclass = subclass, default = default,
    tycons = tycons, abbrs = abbrs, arities = arities};

val tsig0 = make_tsig ([], [], [], [], [], []);


(* sorts *)

fun subsort (TySg {subclass, ...}) (S1, S2) =
  sortorder subclass (S1, S2);

fun norm_sort (TySg {subclass, ...}) S =
  sort_strings (min_sort subclass S);

fun rem_sorts (Type (a, tys)) = Type (a, map rem_sorts tys)
  | rem_sorts (TFree (x, _)) = TFree (x, [])
  | rem_sorts (TVar (xi, _)) = TVar (xi, []);


(* nonempty_sort *)

(* FIXME improve: proper sorts; non-base, non-ground types (vars from hyps) *)
fun nonempty_sort _ _ [] = true
  | nonempty_sort (tsig as TySg {arities, ...}) hyps S =
      exists (exists (fn (c, ss) => [c] = S andalso null ss) o snd) arities
        orelse exists (fn S' => subsort tsig (S', S)) hyps;



(* typ_errors *)

(*check validity of (not necessarily normal) type; accumulate error messages*)

fun typ_errors tsig (typ, errors) =
  let
    val TySg {classes, tycons, abbrs, ...} = tsig;

    fun class_err (errs, c) =
      if c mem_string classes then errs
      else undcl_class c ins_string errs;

    val sort_err = foldl class_err;

    fun typ_errs (Type (c, Us), errs) =
          let
            val errs' = foldr typ_errs (Us, errs);
            fun nargs n =
              if n = length Us then errs'
              else ("Wrong number of arguments: " ^ quote c) ins_string errs';
          in
            (case assoc (tycons, c) of
              Some n => nargs n
            | None =>
                (case assoc (abbrs, c) of
                  Some (vs, _) => nargs (length vs)
                | None => undcl_type c ins_string errs))
          end
    | typ_errs (TFree (_, S), errs) = sort_err (errs, S)
    | typ_errs (TVar ((x, i), S), errs) =
        if i < 0 then
          ("Negative index for TVar " ^ quote x) ins_string sort_err (errs, S)
        else sort_err (errs, S);
  in
    typ_errs (typ, errors)
  end;


(* cert_typ *)

(*check and normalize typ wrt. tsig; errors are indicated by exception TYPE*)

fun cert_typ tsig ty =
  (case typ_errors tsig (ty, []) of
    [] => norm_typ tsig ty
  | errs => raise_type (cat_lines errs) [ty] []);



(** merge type signatures **)

(*'assoc_union' merges two association lists if the contents associated
  the keys are lists*)

fun assoc_union (as1, []) = as1
  | assoc_union (as1, (key, l2) :: as2) =
      (case assoc_string (as1, key) of
        Some l1 => assoc_union 
	              (overwrite (as1, (key, l1 union_string l2)), as2)
      | None => assoc_union ((key, l2) :: as1, as2));


(* merge subclass *)

fun merge_subclass (subclass1, subclass2) =
  let val subclass = transitive_closure (assoc_union (subclass1, subclass2)) 
  in
    if exists (op mem_string) subclass then
      error ("Cyclic class structure!")   (* FIXME improve msg, raise TERM *)
    else subclass
  end;


(* coregularity *)

(* 'is_unique_decl' checks if there exists just one declaration t:(Ss)C *)

fun is_unique_decl ars (t,(C,w)) = case assoc (ars, C) of
      Some(w1) => if w = w1 then () else
        error("There are two declarations\n" ^
              str_of_arity(t, w, [C]) ^ " and\n" ^
              str_of_arity(t, w1, [C]) ^ "\n" ^
              "with the same result class.")
    | None => ();

(* 'coreg' checks if there are two declarations t:(Ss1)C1 and t:(Ss2)C2
   such that C1 >= C2 then Ss1 >= Ss2 (elementwise) *)

fun coreg_err(t, (C1,w1), (C2,w2)) =
    error("Declarations " ^ str_of_arity(t, w1, [C1]) ^ " and "
                          ^ str_of_arity(t, w2, [C2]) ^ " are in conflict");

fun coreg subclass (t, Cw1) =
  let fun check1(Cw1 as (C1,w1), Cw2 as (C2,w2)) =
        if leq subclass (C1,C2)
        then if lew subclass (w1,w2) then () else coreg_err(t, Cw1, Cw2)
        else ()
      fun check(Cw2) = (check1(Cw1,Cw2); check1(Cw2,Cw1))
  in seq check end;

fun add_arity subclass ars (tCw as (_,Cw)) =
      (is_unique_decl ars tCw; coreg subclass tCw ars; Cw ins ars);

fun varying_decls t =
  error ("Type constructor " ^ quote t ^ " has varying number of arguments");


(* 'merge_arities' builds the union of two 'arities' lists;
   it only checks the two restriction conditions and inserts afterwards
   all elements of the second list into the first one *)

fun merge_arities subclass =
  let fun test_ar t (ars1, sw) = add_arity subclass ars1 (t,sw);

      fun merge_c (arities1, (c as (t, ars2))) = case assoc (arities1, t) of
          Some(ars1) =>
            let val ars = foldl (test_ar t) (ars1, ars2)
            in overwrite (arities1, (t,ars)) end
        | None => c::arities1
  in foldl merge_c end;

fun add_tycons (tycons, tn as (t,n)) =
  (case assoc (tycons, t) of
    Some m => if m = n then tycons else varying_decls t
  | None => tn :: tycons);

fun merge_abbrs (abbrs1, abbrs2) =
  let val abbrs = abbrs1 union abbrs2 in
    (case gen_duplicates eq_fst abbrs of
      [] => abbrs
    | dups => raise_term (dup_tyabbrs (map fst dups)) [])
  end;


(* 'merge_tsigs' takes the above declared functions to merge two type
  signatures *)

fun merge_tsigs(TySg{classes=classes1, default=default1, subclass=subclass1,
                     tycons=tycons1, arities=arities1, abbrs=abbrs1},
                TySg{classes=classes2, default=default2, subclass=subclass2,
                     tycons=tycons2, arities=arities2, abbrs=abbrs2}) =
  let val classes' = classes1 union_string classes2;
      val subclass' = merge_subclass (subclass1, subclass2);
      val tycons' = foldl add_tycons (tycons1, tycons2)
      val arities' = merge_arities subclass' (arities1, arities2);
      val default' = min_sort subclass' (default1 @ default2);
      val abbrs' = merge_abbrs(abbrs1, abbrs2);
  in make_tsig(classes', subclass', default', tycons', abbrs', arities') end;



(*** extend type signatures ***)

(** add classes and subclass relations**)

fun add_classes classes cs =
  (case cs inter_string classes of
    [] => cs @ classes
  | dups => err_dup_classes cs);


(*'add_subclass' adds a tuple consisting of a new class (the new class has
  already been inserted into the 'classes' list) and its superclasses (they
  must be declared in 'classes' too) to the 'subclass' list of the given type
  signature; furthermore all inherited superclasses according to the
  superclasses brought with are inserted and there is a check that there are
  no cycles (i.e. C <= D <= C, with C <> D);*)

fun add_subclass classes (subclass, (s, ges)) =
  let
    fun upd (subclass, s') =
      if s' mem_string classes then
        let val ges' = the (assoc (subclass, s))
        in case assoc (subclass, s') of
             Some sups => if s mem_string sups
                           then error(" Cycle :" ^ s^" <= "^ s'^" <= "^ s )
                           else overwrite 
			          (subclass, (s, sups union_string ges'))
           | None => subclass
        end
      else err_undcl_class s'
  in foldl upd (subclass @ [(s, ges)], ges) end;


(* 'extend_classes' inserts all new classes into the corresponding
   lists ('classes', 'subclass') if possible *)

fun extend_classes (classes, subclass, new_classes) =
  let
    val classes' = add_classes classes (map fst new_classes);
    val subclass' = foldl (add_subclass classes') (subclass, new_classes);
  in (classes', subclass') end;


(* ext_tsig_classes *)

fun ext_tsig_classes tsig new_classes =
  let
    val TySg {classes, subclass, default, tycons, abbrs, arities} = tsig;
    val (classes',subclass') = extend_classes (classes,subclass,new_classes);
  in
    make_tsig (classes', subclass', default, tycons, abbrs, arities)
  end;


(* ext_tsig_subclass *)

fun ext_tsig_subclass tsig pairs =
  let
    val TySg {classes, subclass, default, tycons, abbrs, arities} = tsig;

    (* FIXME clean! *)
    val subclass' =
      merge_subclass (subclass, map (fn (c1, c2) => (c1, [c2])) pairs);
  in
    make_tsig (classes, subclass', default, tycons, abbrs, arities)
  end;


(* ext_tsig_defsort *)

fun ext_tsig_defsort(TySg{classes,subclass,tycons,abbrs,arities,...}) default =
  make_tsig (classes, subclass, default, tycons, abbrs, arities);



(** add types **)

fun ext_tsig_types (TySg {classes, subclass, default, tycons, abbrs, arities}) ts =
  let
    fun check_type (c, n) =
      if n < 0 then err_neg_args c
      else if is_some (assoc (tycons, c)) then err_dup_tycon c
      else if is_some (assoc (abbrs, c)) then error (ty_confl c)
      else ();
  in
    seq check_type ts;
    make_tsig (classes, subclass, default, ts @ tycons, abbrs,
      map (rpair [] o #1) ts @ arities)
  end;



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
      if is_none (assoc (tycons, a)) then []
      else [ty_confl a];

    val dup_abbr =
      if is_none (assoc (abbrs, a)) then []
      else ["Duplicate declaration of abbreviation"];
  in
    dup_lhs_vars @ extra_rhs_vars @ tycon_confl @ dup_abbr @
      typ_errors tsig (rhs, [])
  end;

fun prep_abbr tsig (a, vs, raw_rhs) =
  let
    fun err msgs = (seq writeln msgs;
      error ("The error(s) above occurred in type abbreviation " ^ quote a));

    val rhs = rem_sorts (varifyT (no_tvars raw_rhs))
      handle TYPE (msg, _, _) => err [msg];
    val abbr = (a, (vs, rhs));
  in
    (case abbr_errors tsig abbr of
      [] => abbr
    | msgs => err msgs)
  end;

fun add_abbr (tsig as TySg{classes,subclass,default,tycons,arities,abbrs},
              abbr) =
  make_tsig
    (classes,subclass,default,tycons, prep_abbr tsig abbr :: abbrs, arities);

fun ext_tsig_abbrs tsig raw_abbrs = foldl add_abbr (tsig, raw_abbrs);



(** add arities **)

(* 'coregular' checks
   - the two restrictions 'is_unique_decl' and 'coreg'
   - if the classes in the new type declarations are known in the
     given type signature
   - if one type constructor has always the same number of arguments;
   if one type declaration has passed all checks it is inserted into
   the 'arities' association list of the given type signatrure  *)

fun coregular (classes, subclass, tycons) =
  let fun ex C = if C mem_string classes then () else err_undcl_class(C);

      fun addar(arities, (t, (w, C))) = case assoc(tycons, t) of
            Some(n) => if n <> length w then varying_decls(t) else
                     ((seq o seq) ex w; ex C;
                      let val ars = the (assoc(arities, t))
                          val ars' = add_arity subclass ars (t,(C,w))
                      in overwrite(arities, (t,ars')) end)
          | None => error (undcl_type t);

  in addar end;


(* 'close' extends the 'arities' association list after all new type
   declarations have been inserted successfully:
   for every declaration t:(Ss)C , for all classses D with C <= D:
      if there is no declaration t:(Ss')C' with C < C' and C' <= D
      then insert the declaration t:(Ss)D into 'arities'
   this means, if there exists a declaration t:(Ss)C and there is
   no declaration t:(Ss')D with C <=D then the declaration holds
   for all range classes more general than C *)

fun close subclass arities =
  let fun check sl (l, (s, dom)) = case assoc (subclass, s) of
          Some sups =>
            let fun close_sup (l, sup) =
                  if exists (fn s'' => less subclass (s, s'') andalso
                                       leq subclass (s'', sup)) sl
                  then l
                  else (sup, dom)::l
            in foldl close_sup (l, sups) end
        | None => l;
      fun ext (s, l) = (s, foldl (check (map #1 l)) (l, l));
  in map ext arities end;


(* ext_tsig_arities *)

fun ext_tsig_arities tsig sarities =
  let
    val TySg {classes, subclass, default, tycons, arities, abbrs} = tsig;
    val arities1 =
      flat (map (fn (t, ss, cs) => map (fn c => (t, (ss, c))) cs) sarities);
    val arities2 = foldl (coregular (classes, subclass, tycons))
                         (arities, min_domain subclass arities1)
      |> close subclass;
  in
    make_tsig (classes, subclass, default, tycons, abbrs, arities2)
  end;



(*** type unification and inference ***)

(*
  Input:
    - a 'raw' term which contains only dummy types and some explicit type
      constraints encoded as terms.
    - the expected type of the term.

  Output:
    - the correctly typed term
    - the substitution needed to unify the actual type of the term with its
      expected type; only the TVars in the expected type are included.

  During type inference all TVars in the term have index > maxidx, where
  maxidx is the max. index in the expected type of the term (T). This keeps
  them apart, because at the end the type of the term is unified with T.

  1. Add initial type information to the term (attach_types).
     This freezes (freeze_vars) TVars in explicitly provided types (eg
     constraints or defaults) by turning them into TFrees.
  2. Carry out type inference.
  3. Unify actual and expected type.
  4. Turn all local (i.e. > maxidx) TVars into unique new TFrees (freeze).
  5. Thaw all TVars frozen in step 1 (thaw_vars).
*)

(*Raised if types are not unifiable*)
exception TUNIFY;

val tyvar_count = ref 0;

fun tyinit(i) = (tyvar_count := i);

fun new_tvar_inx () = (tyvar_count := !tyvar_count + 1; !tyvar_count)

(*
Generate new TVar.  Index is > maxidx+1 to distinguish it from TVars
generated from variable names (see id_type).
Name is arbitrary because index is new.
*)

fun gen_tyvar(S) = TVar(("'a", new_tvar_inx()), S);

(*Occurs check: type variable occurs in type?*)
fun occ v tye =
  let fun occ(Type(_, Ts)) = exists occ Ts
        | occ(TFree _) = false
        | occ(TVar(w, _)) = v=w orelse
                           (case assoc(tye, w) of
                              None   => false
                            | Some U => occ U);
  in occ end;

(*Chase variable assignments in tye.
  If devar (T, tye) returns a type var then it must be unassigned.*)
fun devar (T as TVar(v, _), tye) = (case  assoc(tye, v)  of
          Some U =>  devar (U, tye)
        | None   =>  T)
  | devar (T, tye) = T;

(* use add_to_tye(t,tye) instead of t::tye
to avoid chains of the form 'a |-> 'b |-> 'c ... *)

fun add_to_tye(p,[]) = [p]
  | add_to_tye(vT as (v,T),(xU as (x,TVar(w,S)))::ps) =
      (if v=w then (x,T) else xU) :: (add_to_tye(vT,ps))
  | add_to_tye(v,x::xs) = x::(add_to_tye(v,xs));

(* 'dom' returns for a type constructor t the list of those domains
   which deliver a given range class C *)

fun dom arities t C = case assoc2 (arities, (t, C)) of
    Some(Ss) => Ss
  | None => raise TUNIFY;


(* 'Dom' returns the union of all domain lists of 'dom' for a given sort S
   (i.e. a set of range classes ); the union is carried out elementwise
   for the seperate sorts in the domains *)

fun Dom (subclass, arities) (t, S) =
  let val domlist = map (dom arities t) S;
  in if null domlist then []
     else foldl (elementwise_union subclass) (hd domlist, tl domlist)
  end;


fun W ((T, S), tsig as TySg{subclass, arities, ...}, tye) =
  let fun Wd ((T, S), tye) = W ((devar (T, tye), S), tsig, tye)
      fun Wk(T as TVar(v, S')) =
              if sortorder subclass (S', S) then tye
              else add_to_tye((v, gen_tyvar(union_sort subclass (S', S))),tye)
        | Wk(T as TFree(v, S')) = if sortorder subclass (S', S) then tye
                                 else raise TUNIFY
        | Wk(T as Type(f, Ts)) =
           if null S then tye
           else foldr Wd (Ts~~(Dom (subclass, arities) (f, S)) , tye)
  in Wk(T) end;


(* Order-sorted Unification of Types (U)  *)

(* Precondition: both types are well-formed w.r.t. type constructor arities *)
fun unify1 (tsig as TySg{subclass, arities, ...}) =
  let fun unif ((T, U), tye) =
        case (devar(T, tye), devar(U, tye)) of
          (T as TVar(v, S1), U as TVar(w, S2)) =>
             if v=w then tye else
             if sortorder subclass (S1, S2) then add_to_tye((w, T),tye) else
             if sortorder subclass (S2, S1) then add_to_tye((v, U),tye)
             else let val nu = gen_tyvar (union_sort subclass (S1, S2))
                  in add_to_tye((v, nu),add_to_tye((w, nu),tye)) end
        | (T as TVar(v, S), U) =>
             if occ v tye U then raise TUNIFY else W ((U,S), tsig, add_to_tye((v, U),tye))
        | (U, T as TVar (v, S)) =>
             if occ v tye U then raise TUNIFY else W ((U,S), tsig, add_to_tye((v, U),tye))
        | (Type(a, Ts), Type(b, Us)) =>
             if a<>b then raise TUNIFY else foldr unif (Ts~~Us, tye)
        | (T, U) => if T=U then tye else raise TUNIFY
  in unif end;

fun unify tsig maxidx tye TU =
  (tyinit maxidx; (unify1 tsig (TU,tye), !tyvar_count) );

(* raw_unify (ignores sorts) *)

fun raw_unify (ty1, ty2) =
  (unify tsig0 0 [] (rem_sorts ty1, rem_sorts ty2); true)
    handle TUNIFY => false;


(*Type inference for polymorphic term*)
fun infer tsig =
  let fun inf(Ts, Const (_, T), tye) = (T, tye)
        | inf(Ts, Free  (_, T), tye) = (T, tye)
        | inf(Ts, Bound i, tye) = ((nth_elem(i, Ts) , tye)
          handle LIST _=> raise TYPE ("loose bound variable", [], [Bound i]))
        | inf(Ts, Var (_, T), tye) = (T, tye)
        | inf(Ts, Abs (_, T, body), tye) =
            let val (U, tye') = inf(T::Ts, body, tye) in  (T-->U, tye')  end
        | inf(Ts, f$u, tye) =
            let val (U, tyeU) = inf(Ts, u, tye);
                val (T, tyeT) = inf(Ts, f, tyeU);
                fun err s =
                  raise TYPE(s, [inst_typ tyeT T, inst_typ tyeT U], [f$u])
		val msg = "function type is incompatible with argument type"
            in case T of
                 Type("fun", [T1, T2]) =>
                   ( (T2, unify1 tsig ((T1, U), tyeT))
                     handle TUNIFY => err msg)
               | TVar _ =>
                   let val T2 = gen_tyvar([])
                   in (T2, unify1 tsig ((T, U-->T2), tyeT))
                      handle TUNIFY => err msg
                   end
               | _ => err"function type is expected in application"
           end
  in inf end;

val freeze_vars =
      map_type_tvar (fn (v, S) => TFree(Syntax.string_of_vname v, S));

(* Attach a type to a constant *)
fun type_const (a, T) = Const(a, incr_tvar (new_tvar_inx()) T);

(*Find type of ident.  If not in table then use ident's name for tyvar
  to get consistent typing.*)
fun new_id_type a = TVar(("'"^a, new_tvar_inx()), []);

fun type_of_ixn(types, ixn as (a, _),maxidx1) =
  case types ixn of Some T => freeze_vars T
                  | None   => TVar(("'"^a, maxidx1), []);

fun constrain (term, T) = Const (Syntax.constrainC, T --> T) $ term;

fun constrainAbs (Abs (a, _, body), T) = Abs (a, T, body)
  | constrainAbs _ = sys_error "constrainAbs";


(* attach_types *)

(*
  Attach types to a term. Input is a "parse tree" containing dummy types.
  Type constraints are translated and checked for validity wrt tsig. TVars in
  constraints are frozen.

  The atoms in the resulting term satisfy the following spec:

  Const (a, T):
    T is a renamed copy of the generic type of a; renaming increases index of
    all TVars by new_tvar_inx(), which is > maxidx+1.

  Free (a, T), Var (ixn, T):
    T is either the frozen default type of a or TVar (("'"^a, maxidx+1), [])

  Abs (a, T, _):
    T is either a type constraint or TVar (("'" ^ a, i), []), where i is
    generated by new_tvar_inx(). Thus different abstractions can have the
    bound variables of the same name but different types.
*)

(* FIXME consistency of sort_env / sorts (!?) *)

fun attach_types (tsig, const_type, types, sorts, maxidx1) tm =
  let
    val sort_env = Syntax.raw_term_sorts tm;
    fun def_sort xi = if_none (sorts xi) (defaultS tsig);

    fun prepareT t =
      freeze_vars (cert_typ tsig (Syntax.typ_of_term sort_env def_sort t));

    fun add (Const (a, _)) =
          (case const_type a of
            Some T => type_const (a, T)
          | None => raise_type ("No such constant: " ^ quote a) [] [])
      | add (Free (a, _)) =
          (case const_type a of
            Some T => type_const (a, T)
          | None => Free (a, type_of_ixn (types,(a,~1),maxidx1)))
      | add (Var (ixn, _)) = Var (ixn, type_of_ixn (types, ixn, maxidx1))
      | add (Bound i) = Bound i
      | add (Abs (a, _, body)) = Abs (a, new_id_type a, add body)
      | add ((f as Const (a, _) $ t1) $ t2) =
          if a = Syntax.constrainC then
            constrain (add t1, prepareT t2)
          else if a = Syntax.constrainAbsC then
            constrainAbs (add t1, prepareT t2)
          else add f $ add t2
      | add (f $ t) = add f $ add t;
  in add tm end;


(* Post-Processing *)

(*Instantiation of type variables in terms*)
fun inst_types tye = map_term_types (inst_typ tye);

(*Delete explicit constraints -- occurrences of "_constrain" *)
fun unconstrain (Abs(a, T, t)) = Abs(a, T, unconstrain t)
  | unconstrain ((f as Const(a, _)) $ t) =
      if a=Syntax.constrainC then unconstrain t
      else unconstrain f $ unconstrain t
  | unconstrain (f$t) = unconstrain f $ unconstrain t
  | unconstrain (t) = t;

fun nextname(pref,c) = if c="z" then (pref^"a", "a") else (pref,chr(ord(c)+1));

fun newtvars used =
  let fun new([],_,vmap) = vmap
        | new(ixn::ixns,p as (pref,c),vmap) =
            let val nm = pref ^ c
            in if nm mem_string used then new(ixn::ixns,nextname p, vmap)
               else new(ixns, nextname p, (ixn,nm)::vmap)
            end
  in new end;

(*
Turn all TVars which satisfy p into new (if freeze then TFrees else TVars).
Note that if t contains frozen TVars there is the possibility that a TVar is
turned into one of those. This is sound but not complete.
*)
fun convert used freeze p t =
  let val used = if freeze then add_term_tfree_names(t, used)
                 else used union
                      (map #1 (filter_out p (add_term_tvar_ixns(t, []))))
      val ixns = filter p (add_term_tvar_ixns(t, []));
      val vmap = newtvars used (ixns,("'","a"),[]);
      fun conv(var as (ixn,S)) = case assoc(vmap,ixn) of
            None => TVar(var) |
            Some(a) => if freeze then TFree(a,S) else TVar((a,0),S);
  in map_term_types (map_type_tvar conv) t end;

fun freeze t = convert (add_term_tfree_names(t,[])) true (K true) t;

(* Thaw all TVars that were frozen in freeze_vars *)
val thaw_vars =
  let fun thaw(f as (a, S)) = (case explode a of
          "?"::"'"::vn => let val ((b, i), _) = Syntax.scan_varname vn
                          in TVar(("'"^b, i), S) end
        | _ => TFree f)
  in map_type_tfree thaw end;


fun restrict maxidx1 tye =
  let fun clean(tye1, ((a, i), T)) =
        if i >= maxidx1 then tye1 else ((a, i), inst_typ tye T) :: tye1
  in foldl clean ([], tye) end


(*Infer types for terms.  Given Ts=[T1,...,Tn] and ts=[t1,...,tn], ensure that
	the type of ti unifies with Ti (i=1,...,n).
  types is a partial map from indexnames to types (constrains Free, Var).
  sorts is a partial map from indexnames to sorts (constrains TFree, TVar).
  used is the list of already used type variables.
  If freeze then internal TVars are turned into TFrees, else TVars.*)
fun infer_types (tsig, const_type, types, sorts, used, freeze, Ts, ts) =
  let
    val maxidx1 = maxidx_of_typs Ts + 1;
    val () = tyinit(maxidx1+1);
    val us = map (attach_types (tsig, const_type, types, sorts, maxidx1)) ts;
    val u = list_comb(Const("",Ts ---> propT),us)
    val (_, tye) = infer tsig ([], u, []);
    val uu = unconstrain u;
    val Ttye = restrict maxidx1 tye (*restriction to TVars in Ts*)
    val all = Const("", Type("", map snd Ttye)) $ (inst_types tye uu)
      (*all is a dummy term which contains all exported TVars*)
    val Const(_, Type(_, Us)) $ u'' =
      map_term_types thaw_vars (convert used freeze (fn (_,i) => i >= maxidx1) all)
      (*convert all internally generated TVars into TFrees or TVars
        and thaw all initially frozen TVars*)
  in
    (snd(strip_comb u''), (map fst Ttye) ~~ Us)
  end;

end;
