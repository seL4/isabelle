(*  Title:      Pure/sign.ML
    ID:         $Id$
    Author:     Lawrence C Paulson and Markus Wenzel

The abstract type "sg" of signatures.
*)

(*external forms*)
type xstring = string;
type xclass = class;
type xsort = sort;
type xtyp = typ;
type xterm = term;

signature SIGN =
sig
  type sg
  val rep_sg: sg ->
   {tsig: Type.type_sig,
    const_tab: typ Symtab.table,
    syn: Syntax.syntax,
    path: string list,
    spaces: (string * NameSpace.T) list,
    stamps: string ref list}
  val subsig: sg * sg -> bool
  val eq_sg: sg * sg -> bool
  val same_sg: sg * sg -> bool
  val is_draft: sg -> bool
  val const_type: sg -> string -> typ option
  val classes: sg -> class list
  val subsort: sg -> sort * sort -> bool
  val nodup_Vars: term -> unit
  val norm_sort: sg -> sort -> sort
  val nonempty_sort: sg -> sort list -> sort -> bool
  val long_names: bool ref
  val classK: string
  val typeK: string
  val constK: string
  val intern: sg -> string -> xstring -> string
  val extern: sg -> string -> string -> xstring
  val full_name: sg -> xstring -> string
  val intern_class: sg -> xclass -> class
  val extern_class: sg -> class -> xclass
  val intern_sort: sg -> xsort -> sort
  val extern_sort: sg -> sort -> xsort
  val intern_typ: sg -> xtyp -> typ
  val extern_typ: sg -> typ -> xtyp
  val intern_term: sg -> xterm -> term
  val extern_term: sg -> term -> xterm
  val intern_tycons: sg -> xtyp -> typ
  val intern_tycon: sg -> xstring -> string
  val intern_const: sg -> xstring -> string
  val print_sg: sg -> unit
  val pretty_sg: sg -> Pretty.T
  val pprint_sg: sg -> pprint_args -> unit
  val pretty_term: sg -> term -> Pretty.T
  val pretty_typ: sg -> typ -> Pretty.T
  val pretty_sort: sg -> sort -> Pretty.T
  val string_of_term: sg -> term -> string
  val string_of_typ: sg -> typ -> string
  val string_of_sort: sg -> sort -> string
  val pprint_term: sg -> term -> pprint_args -> unit
  val pprint_typ: sg -> typ -> pprint_args -> unit
  val certify_typ: sg -> typ -> typ
  val certify_term: sg -> term -> term * typ * int
  val read_typ: sg * (indexname -> sort option) -> string -> typ
  val infer_types: sg -> (indexname -> typ option) ->
    (indexname -> sort option) -> string list -> bool
    -> xterm list * typ -> int * term * (indexname * typ) list
  val add_classes: (xclass * xclass list) list -> sg -> sg
  val add_classes_i: (xclass * class list) list -> sg -> sg
  val add_classrel: (xclass * xclass) list -> sg -> sg
  val add_classrel_i: (class * class) list -> sg -> sg
  val add_defsort: xsort -> sg -> sg
  val add_defsort_i: sort -> sg -> sg
  val add_types: (xstring * int * mixfix) list -> sg -> sg
  val add_tyabbrs: (xstring * string list * string * mixfix) list -> sg -> sg
  val add_tyabbrs_i: (xstring * string list * typ * mixfix) list -> sg -> sg
  val add_arities: (xstring * xsort list * xsort) list -> sg -> sg
  val add_arities_i: (string * sort list * sort) list -> sg -> sg
  val add_consts: (xstring * string * mixfix) list -> sg -> sg
  val add_consts_i: (xstring * typ * mixfix) list -> sg -> sg
  val add_syntax: (xstring * string * mixfix) list -> sg -> sg
  val add_syntax_i: (xstring * typ * mixfix) list -> sg -> sg
  val add_modesyntax: (string * bool) * (xstring * string * mixfix) list -> sg -> sg
  val add_modesyntax_i: (string * bool) * (xstring * typ * mixfix) list -> sg -> sg
  val add_trfuns:
    (string * (ast list -> ast)) list *
    (string * (term list -> term)) list *
    (string * (term list -> term)) list *
    (string * (ast list -> ast)) list -> sg -> sg
  val add_trfunsT:
    (string * (typ -> term list -> term)) list -> sg -> sg
  val add_tokentrfuns:
    (string * string * (string -> string * int)) list -> sg -> sg
  val add_trrules: (string * string) Syntax.trrule list -> sg -> sg
  val add_trrules_i: ast Syntax.trrule list -> sg -> sg
  val add_path: string -> sg -> sg
  val add_space: string * string list -> sg -> sg
  val add_name: string -> sg -> sg
  val make_draft: sg -> sg
  val merge: sg * sg -> sg
  val proto_pure: sg
  val pure: sg
  val cpure: sg
  val const_of_class: class -> string
  val class_of_const: string -> class
end;

structure Sign : SIGN =
struct

(** datatype sg **)

datatype sg =
  Sg of {
    tsig: Type.type_sig,                        (*order-sorted signature of types*)
    const_tab: typ Symtab.table,                (*type schemes of constants*)
    syn: Syntax.syntax,                         (*syntax for parsing and printing*)
    path: string list,                     	(*current name space entry prefix*)
    spaces: (string * NameSpace.T) list,   	(*name spaces for consts, types etc.*)
    stamps: string ref list};                   (*unique theory indentifier*)

    (*the "ref" in stamps ensures that no two signatures are identical
      -- it is impossible to forge a signature*)

fun rep_sg (Sg args) = args;
val tsig_of = #tsig o rep_sg;


(* inclusion and equality *)

local
  (*avoiding polymorphic equality: factor 10 speedup*)
  fun mem_stamp (_:string ref, []) = false
    | mem_stamp (x, y :: ys) = x = y orelse mem_stamp (x, ys);

  fun subset_stamp ([], ys) = true
    | subset_stamp (x :: xs, ys) =
        mem_stamp (x, ys) andalso subset_stamp (xs, ys);

  (*fast partial test*)
  fun fast_sub ([]: string ref list, _) = true
    | fast_sub (_, []) = false
    | fast_sub (x :: xs, y :: ys) =
        if x = y then fast_sub (xs, ys)
        else fast_sub (x :: xs, ys);
in
  fun subsig (Sg {stamps = s1, ...}, Sg {stamps = s2, ...}) =
    s1 = s2 orelse subset_stamp (s1, s2);

  fun fast_subsig (Sg {stamps = s1, ...}, Sg {stamps = s2, ...}) =
    s1 = s2 orelse fast_sub (s1, s2);

  fun eq_sg (Sg {stamps = s1, ...}, Sg {stamps = s2, ...}) =
    s1 = s2 orelse (subset_stamp (s1, s2) andalso subset_stamp (s2, s1));
end;


(*test if same theory names are contained in signatures' stamps,
  i.e. if signatures belong to same theory but not necessarily to the
  same version of it*)
fun same_sg (Sg {stamps = s1, ...}, Sg {stamps = s2, ...}) =
  eq_set_string (pairself (map (op !)) (s1, s2));

(*test for drafts*)
fun is_draft (Sg {stamps = ref "#" :: _, ...}) = true
  | is_draft _ = false;


(* consts *)

fun const_type (Sg {const_tab, ...}) c = Symtab.lookup (const_tab, c);


(* classes and sorts *)

val classes = #classes o Type.rep_tsig o tsig_of;

val subsort = Type.subsort o tsig_of;
val norm_sort = Type.norm_sort o tsig_of;
val nonempty_sort = Type.nonempty_sort o tsig_of;



(** name spaces **)

(*prune names on output by default*)
val long_names = ref false;


(* kinds *)

val classK = "class";
val typeK = "type";
val constK = "const";


(* add and retrieve names *)

fun space_of spaces kind =
  if_none (assoc (spaces, kind)) NameSpace.empty;

(*input and output of qualified names*)
fun intrn spaces kind = NameSpace.lookup (space_of spaces kind);
fun extrn spaces kind = NameSpace.prune (space_of spaces kind);

(*add names*)
fun add_names spaces kind names =
  let val space' = NameSpace.extend (names, space_of spaces kind) in
    overwrite (spaces, (kind, space'))
  end;

(*make full names*)
fun full path name = NameSpace.pack (path @ NameSpace.unpack name);


(* intern / extern names *)

local

  fun add_typ_classes (Type (_, Ts), cs) = foldr add_typ_classes (Ts, cs)
    | add_typ_classes (TFree (_, S), cs) = S union cs
    | add_typ_classes (TVar (_, S), cs) = S union cs;

  fun add_typ_tycons (Type (c, Ts), cs) = foldr add_typ_tycons (Ts, c ins cs)
    | add_typ_tycons (_, cs) = cs;

  val add_term_classes = it_term_types add_typ_classes;
  val add_term_tycons = it_term_types add_typ_tycons;

  fun add_term_consts (Const (c, _), cs) = c ins cs
    | add_term_consts (t $ u, cs) = add_term_consts (t, add_term_consts (u, cs))
    | add_term_consts (Abs (_, _, t), cs) = add_term_consts (t, cs)
    | add_term_consts (_, cs) = cs;


  (*map classes, tycons*)
  fun map_typ f g (Type (c, Ts)) = Type (g c, map (map_typ f g) Ts)
    | map_typ f _ (TFree (x, S)) = TFree (x, map f S)
    | map_typ f _ (TVar (xi, S)) = TVar (xi, map f S);

  (*map classes, tycons, consts*)
  fun map_term f g h (Const (c, T)) = Const (h c, map_typ f g T)
    | map_term f g _ (Free (x, T)) = Free (x, map_typ f g T)
    | map_term f g _ (Var (xi, T)) = Var (xi, map_typ f g T)
    | map_term _ _ _ (t as Bound _) = t
    | map_term f g h (Abs (x, T, t)) = Abs (x, map_typ f g T, map_term f g h t)
    | map_term f g h (t $ u) = map_term f g h t $ map_term f g h u;

  (*prepare mapping of names*)
  fun mapping f add_xs t =
    let
      fun f' x = let val y = f x in if x = y then None else Some (x, y) end;
      val table = mapfilter f' (add_xs (t, []));
      fun lookup x = if_none (assoc (table, x)) x;
    in lookup end;

  (*intern / extern typ*)
  fun trn_typ trn T =
    T |> map_typ
      (mapping (trn classK) add_typ_classes T)
      (mapping (trn typeK) add_typ_tycons T);

  (*intern / extern term*)
  fun trn_term trn t =
    t |> map_term
      (mapping (trn classK) add_term_classes t)
      (mapping (trn typeK) add_term_tycons t)
      (mapping (trn constK) add_term_consts t);


  fun spaces_of (Sg {spaces, ...}) = spaces;

in

  fun intrn_class spaces = intrn spaces classK;
  fun extrn_class spaces = extrn spaces classK;
  val intrn_sort = map o intrn_class;
  val extrn_sort = map o extrn_class;
  val intrn_typ = trn_typ o intrn;
  val extrn_typ = trn_typ o extrn;
  val intrn_term = trn_term o intrn;
  val extrn_term = trn_term o extrn;

  fun intrn_tycons spaces T =
    map_typ I (mapping (intrn spaces typeK) add_typ_tycons T) T;

  val intern = intrn o spaces_of;
  val extern = intrn o spaces_of;
  val intern_class = intrn_class o spaces_of;
  val extern_class = extrn_class o spaces_of;
  val intern_sort = intrn_sort o spaces_of;
  val extern_sort = extrn_sort o spaces_of;
  val intern_typ = intrn_typ o spaces_of;
  val extern_typ = extrn_typ o spaces_of;
  val intern_term = intrn_term o spaces_of;
  val extern_term = extrn_term o spaces_of;

  fun intern_tycon sg = intrn (spaces_of sg) typeK;
  fun intern_const sg = intrn (spaces_of sg) constK;
  val intern_tycons = intrn_tycons o spaces_of;

  fun full_name (Sg {path, ...}) = full path;
end;



(** print signature **)

fun stamp_names stamps = rev (map ! stamps);

fun print_sg sg =
  let
    val Sg {syn, ...} = sg;

    fun prt_typ ty = Pretty.quote (Syntax.pretty_typ syn ty);
    fun prt_cls c = Syntax.pretty_sort syn [c];

    fun pretty_space (kind, space) = Pretty.block (Pretty.breaks
      (map Pretty.str (kind ^ ":" :: map quote (NameSpace.dest space))));

    fun pretty_classes cs = Pretty.block
      (Pretty.breaks (Pretty.str "classes:" :: map prt_cls cs));

    fun pretty_classrel (c, cs) = Pretty.block
      (prt_cls c :: Pretty.str " <" :: Pretty.brk 1 ::
        Pretty.commas (map prt_cls cs));

    fun pretty_default S = Pretty.block
      [Pretty.str "default:", Pretty.brk 1, Syntax.pretty_sort syn S];

    fun pretty_ty (ty, n) = Pretty.str (ty ^ " " ^ string_of_int n);

    fun pretty_abbr (ty, (vs, rhs)) = Pretty.block
      [prt_typ (Type (ty, map (fn v => TVar ((v, 0), [])) vs)),
        Pretty.str " =", Pretty.brk 1, prt_typ rhs];

    fun pretty_arity ty (c, []) = Pretty.block
          [Pretty.str (ty ^ " ::"), Pretty.brk 1, prt_cls c]
      | pretty_arity ty (c, Ss) = Pretty.block
          [Pretty.str (ty ^ " ::"), Pretty.brk 1,
            Pretty.list "(" ")" (map (Syntax.pretty_sort syn) Ss),
            Pretty.brk 1, prt_cls c];

    fun pretty_arities (ty, ars) = map (pretty_arity ty) ars;

    fun pretty_const (c, ty) = Pretty.block
      [Pretty.str (quote c ^ " ::"), Pretty.brk 1, prt_typ ty];

    val Sg {tsig, const_tab, syn = _, path, spaces, stamps} = sg;
    val spaces' = sort (fn ((k1, _), (k2, _)) => k1 < k2) spaces;
    val {classes, classrel, default, tycons, abbrs, arities} =
      Type.rep_tsig tsig;
  in
    Pretty.writeln (Pretty.strs ("stamps:" :: stamp_names stamps));
    Pretty.writeln (Pretty.strs ["name entry path:", NameSpace.pack path]);
    Pretty.writeln (Pretty.big_list "name spaces:" (map pretty_space spaces'));
    Pretty.writeln (pretty_classes classes);
    Pretty.writeln (Pretty.big_list "class relation:" (map pretty_classrel classrel));
    Pretty.writeln (pretty_default default);
    Pretty.writeln (Pretty.big_list "type constructors:" (map pretty_ty tycons));
    Pretty.writeln (Pretty.big_list "type abbreviations:" (map pretty_abbr abbrs));
    Pretty.writeln (Pretty.big_list "type arities:" (flat (map pretty_arities arities)));
    Pretty.writeln (Pretty.big_list "consts:" (map pretty_const (Symtab.dest const_tab)))
  end;


fun pretty_sg (Sg {stamps, ...}) =
  Pretty.str_list "{" "}" (stamp_names stamps);

val pprint_sg = Pretty.pprint o pretty_sg;



(** pretty printing of terms and types **)

fun pretty_term (Sg {syn, spaces, stamps, ...}) t =
  Syntax.pretty_term syn
    ("CPure" mem_string (map ! stamps))
    (if ! long_names then t else extrn_term spaces t);

fun pretty_typ (Sg {syn, spaces, ...}) T =
  Syntax.pretty_typ syn
    (if ! long_names then T else extrn_typ spaces T);

fun pretty_sort (Sg {syn, spaces, ...}) S =
  Syntax.pretty_sort syn
    (if ! long_names then S else extrn_sort spaces S);


fun string_of_term sg t = Pretty.string_of (pretty_term sg t);
fun string_of_typ sg T = Pretty.string_of (pretty_typ sg T);
fun string_of_sort sg S = Pretty.string_of (pretty_sort sg S);

fun pprint_term sg = Pretty.pprint o Pretty.quote o (pretty_term sg);
fun pprint_typ sg = Pretty.pprint o Pretty.quote o (pretty_typ sg);



(** read types **)  (*exception ERROR*)

fun err_in_type s =
  error ("The error(s) above occurred in type " ^ quote s);

fun read_raw_typ syn tsig spaces def_sort str =
  intrn_tycons spaces
    (Syntax.read_typ syn (Type.get_sort tsig def_sort (intrn_sort spaces)) str
      handle ERROR => err_in_type str);
  
(*read and certify typ wrt a signature*)
fun read_typ (Sg {tsig, syn, spaces, ...}, def_sort) str =
  Type.cert_typ tsig (read_raw_typ syn tsig spaces def_sort str)
    handle TYPE (msg, _, _) => (error_msg msg; err_in_type str);



(** certify types and terms **)   (*exception TYPE*)

fun certify_typ (Sg {tsig, ...}) ty = Type.cert_typ tsig ty;

(*check for duplicate TVars with distinct sorts*)
fun nodup_TVars (tvars, T) =
  (case T of
    Type (_, Ts) => nodup_TVars_list (tvars, Ts)
  | TFree _ => tvars
  | TVar (v as (a, S)) =>
      (case assoc_string_int (tvars, a) of
        Some S' =>
          if S = S' then tvars
          else raise TYPE ("Type variable " ^ Syntax.string_of_vname a ^
            " has two distinct sorts", [TVar (a, S'), T], [])
      | None => v :: tvars))
(*equivalent to foldl nodup_TVars_list, but 3X faster under Poly/ML*)
and nodup_TVars_list (tvars, []) = tvars
  | nodup_TVars_list (tvars, T :: Ts) =
      nodup_TVars_list (nodup_TVars (tvars, T), Ts);

(*check for duplicate Vars with distinct types*)
fun nodup_Vars tm =
  let
    fun nodups vars tvars tm =
      (case tm of
        Const (c, T) => (vars, nodup_TVars (tvars, T))
      | Free (a, T) => (vars, nodup_TVars (tvars, T))
      | Var (v as (ixn, T)) =>
          (case assoc_string_int (vars, ixn) of
            Some T' =>
              if T = T' then (vars, nodup_TVars (tvars, T))
              else raise TYPE ("Variable " ^ Syntax.string_of_vname ixn ^
                " has two distinct types", [T', T], [])
          | None => (v :: vars, tvars))
      | Bound _ => (vars, tvars)
      | Abs (_, T, t) => nodups vars (nodup_TVars (tvars, T)) t
      | s $ t =>
          let val (vars',tvars') = nodups vars tvars s in
            nodups vars' tvars' t
          end);
  in nodups [] [] tm; () end;


fun mapfilt_atoms f (Abs (_, _, t)) = mapfilt_atoms f t
  | mapfilt_atoms f (t $ u) = mapfilt_atoms f t @ mapfilt_atoms f u
  | mapfilt_atoms f a = (case f a of Some y => [y] | None => []);


fun certify_term (sg as Sg {tsig, ...}) tm =
  let
    fun valid_const a T =
      (case const_type sg a of
        Some U => Type.typ_instance (tsig, T, U)
      | _ => false);

    fun atom_err (Const (a, T)) =
          if valid_const a T then None
          else Some ("Illegal type for constant " ^ quote a ^ " :: " ^
            quote (string_of_typ sg T))
      | atom_err (Var ((x, i), _)) =
          if i < 0 then Some ("Negative index for Var " ^ quote x) else None
      | atom_err _ = None;

    val norm_tm =
      (case it_term_types (Type.typ_errors tsig) (tm, []) of
        [] => map_term_types (Type.norm_typ tsig) tm
      | errs => raise TYPE (cat_lines errs, [], [tm]));
    val _ = nodup_Vars norm_tm;
  in
    (case mapfilt_atoms atom_err norm_tm of
      [] => (norm_tm, type_of norm_tm, maxidx_of_term norm_tm)
    | errs => raise TYPE (cat_lines errs, [], [norm_tm]))
  end;



(** infer_types **)         (*exception ERROR*)

(*
  ts: list of alternative parses (hopefully only one is type-correct)
  T: expected type

  def_type: partial map from indexnames to types (constrains Frees, Vars)
  def_sort: partial map from indexnames to sorts (constrains TFrees, TVars)
  used: list of already used type variables
  freeze: if true then generated parameters are turned into TFrees, else TVars
*)

fun infer_types sg def_type def_sort used freeze (ts, T) =
  let
    val Sg {tsig, ...} = sg;
    val prt =
      setmp Syntax.show_brackets true
        (setmp long_names true (pretty_term sg));
    val prT = setmp long_names true (pretty_typ sg);
    val infer = Type.infer_types prt prT tsig (const_type sg) def_type def_sort
      (intern_const sg) (intern_tycons sg) (intern_sort sg) used freeze;

    val T' = certify_typ sg T handle TYPE (msg, _, _) => error msg;

    fun warn () =
      if length ts > 1 andalso length ts <= ! Syntax.ambiguity_level
      then (*no warning shown yet*)
        warning "Got more than one parse tree.\n\
          \Retry with smaller Syntax.ambiguity_level for more information."
      else ();

    datatype result =
      One of int * term * (indexname * typ) list |
      Errs of string list |
      Ambigs of term list;

    fun process_term (res, (t, i)) =
      let val ([u], tye) = infer [T'] [t] in
        (case res of
          One (_, t0, _) => Ambigs ([u, t0])
        | Errs _ => One (i, u, tye)
        | Ambigs us => Ambigs (u :: us))
      end handle TYPE (msg, _, _) =>
        (case res of
          Errs errs => Errs (msg :: errs)
        | _ => res);
  in
    (case foldl process_term (Errs [], ts ~~ (0 upto (length ts - 1))) of
      One res =>
       (if length ts > ! Syntax.ambiguity_level then
          warning "Fortunately, only one parse tree is type correct.\n\
            \You may still want to disambiguate your grammar or your input."
        else (); res)
    | Errs errs => (warn (); error (cat_lines errs))
    | Ambigs us =>
        (warn (); error ("More than one term is type correct:\n" ^
          (cat_lines (map (Pretty.string_of o prt) us)))))
  end;



(** extend signature **)    (*exception ERROR*)

(** signature extension functions **)  (*exception ERROR*)

fun decls_of path name_of mfixs =
  map (fn (x, y, mx) => (full path (name_of x mx), y)) mfixs;

fun no_read _ _ _ decl = decl;


(* add default sort *)

fun ext_defsort int (syn, tsig, ctab, (path, spaces)) S =
  (syn, Type.ext_tsig_defsort tsig (if int then intrn_sort spaces S else S),
    ctab, (path, spaces));


(* add type constructors *)

fun ext_types (syn, tsig, ctab, (path, spaces)) types =
  let val decls = decls_of path Syntax.type_name types in
    (Syntax.extend_type_gram syn types,
      Type.ext_tsig_types tsig decls, ctab,
      (path, add_names spaces typeK (map fst decls)))
  end;


(* add type abbreviations *)

fun read_abbr syn tsig spaces (t, vs, rhs_src) =
  (t, vs, read_raw_typ syn tsig spaces (K None) rhs_src)
    handle ERROR => error ("in type abbreviation " ^ t);

fun ext_abbrs rd_abbr (syn, tsig, ctab, (path, spaces)) abbrs =
  let
    fun mfix_of (t, vs, _, mx) = (t, length vs, mx);
    val syn' = Syntax.extend_type_gram syn (map mfix_of abbrs);

    val abbrs' =
      map (fn (t, vs, rhs, mx) =>
        (full path (Syntax.type_name t mx), vs, rhs)) abbrs;
    val spaces' = add_names spaces typeK (map #1 abbrs');
    val decls = map (rd_abbr syn' tsig spaces') abbrs';
  in
    (syn', Type.ext_tsig_abbrs tsig decls, ctab, (path, spaces'))
  end;

fun ext_tyabbrs abbrs = ext_abbrs read_abbr abbrs;
fun ext_tyabbrs_i abbrs = ext_abbrs no_read abbrs;


(* add type arities *)

fun ext_arities int (syn, tsig, ctab, (path, spaces)) arities =
  let
    fun intrn_arity (c, Ss, S) =
      (intrn spaces typeK c, map (intrn_sort spaces) Ss, intrn_sort spaces S);
    val intrn = if int then map intrn_arity else I;
    val tsig' = Type.ext_tsig_arities tsig (intrn arities);
    val log_types = Type.logical_types tsig';
  in
    (Syntax.extend_log_types syn log_types, tsig', ctab, (path, spaces))
  end;


(* add term constants and syntax *)

fun const_name path c mx =
  full path (Syntax.const_name c mx);

fun err_in_const c =
  error ("in declaration of constant " ^ quote c);

fun err_dup_consts cs =
  error ("Duplicate declaration of constant(s) " ^ commas_quote cs);


fun read_const syn tsig (path, spaces) (c, ty_src, mx) =
  (c, read_raw_typ syn tsig spaces (K None) ty_src, mx)
    handle ERROR => err_in_const (const_name path c mx);

fun ext_cnsts rd_const syn_only prmode (syn, tsig, ctab, (path, spaces)) raw_consts =
  let
    fun prep_const (c, ty, mx) =
      (c, compress_type (Type.varifyT (Type.cert_typ tsig (Type.no_tvars ty))), mx)
        handle TYPE (msg, _, _) =>
          (error_msg msg; err_in_const (const_name path c mx));

    val consts = map (prep_const o rd_const syn tsig (path, spaces)) raw_consts;
    val decls =
      if syn_only then []
      else decls_of path Syntax.const_name consts;
  in
    (Syntax.extend_const_gram syn prmode consts, tsig,
      Symtab.extend_new (ctab, decls)
        handle Symtab.DUPS cs => err_dup_consts cs,
      (path, add_names spaces constK (map fst decls)))
  end;

val ext_consts_i = ext_cnsts no_read false ("", true);
val ext_consts = ext_cnsts read_const false ("", true);
val ext_syntax_i = ext_cnsts no_read true ("", true);
val ext_syntax = ext_cnsts read_const true ("", true);
fun ext_modesyntax_i sg (prmode, consts) = ext_cnsts no_read true prmode sg consts;
fun ext_modesyntax sg (prmode, consts) = ext_cnsts read_const true prmode sg consts;


(* add type classes *)

fun const_of_class c = c ^ "_class";

fun class_of_const c_class =
  let
    val c = implode (take (size c_class - size "_class", explode c_class));
  in
    if const_of_class c = c_class then c
    else raise TERM ("class_of_const: bad name " ^ quote c_class, [])
  end;


fun ext_classes int (syn, tsig, ctab, (path, spaces)) classes =
  let
    val names = map fst classes;
    val consts =
      map (fn c => (const_of_class c, a_itselfT --> propT, NoSyn)) names;

    val full_names = map (full path) names;
    val spaces' = add_names spaces classK full_names;
    val intrn = if int then map (intrn_class spaces') else I;
    val classes' =
      ListPair.map (fn (c, (_, cs)) => (c, intrn cs)) (full_names, classes);
  in
    ext_consts_i
      (Syntax.extend_consts syn names,
        Type.ext_tsig_classes tsig classes', ctab, (path, spaces'))
    consts
  end;


(* add to classrel *)

fun ext_classrel int (syn, tsig, ctab, (path, spaces)) pairs =
  let val intrn = if int then map (pairself (intrn_class spaces)) else I in
    (syn, Type.ext_tsig_classrel tsig (intrn pairs), ctab, (path, spaces))
  end;


(* add to syntax *)

fun ext_syn extfun (syn, tsig, ctab, names) args =
  (extfun syn args, tsig, ctab, names);


(* add to path *)

fun ext_path (syn, tsig, ctab, (path, spaces)) elem =
  let
    val path' =
      if elem = ".." andalso not (null path) then fst (split_last path)
      else if elem = "/" then []
      else path @ NameSpace.unpack elem;
  in
    (syn, tsig, ctab, (path', spaces))
  end;      


(* add to name space *)

fun ext_space (syn, tsig, ctab, (path, spaces)) (kind, names) =
  (syn, tsig, ctab, (path, add_names spaces kind names));


(* build signature *)

fun ext_stamps stamps name =
  let
    val stmps = (case stamps of ref "#" :: ss => ss | ss => ss);
  in
    if exists (equal name o !) stmps then
      error ("Theory already contains a " ^ quote name ^ " component")
    else ref name :: stmps
  end;

fun make_sign (syn, tsig, ctab, (path, spaces)) stamps name =
  Sg {tsig = tsig, const_tab = ctab, syn = syn, path = path, spaces = spaces,
    stamps = ext_stamps stamps name};

fun extend_sign extfun name decls (Sg {tsig, const_tab, syn, path, spaces, stamps}) =
  make_sign (extfun (syn, tsig, const_tab, (path, spaces)) decls) stamps name;


(* the external interfaces *)

val add_classes      = extend_sign (ext_classes true) "#";
val add_classes_i    = extend_sign (ext_classes false) "#";
val add_classrel     = extend_sign (ext_classrel true) "#";
val add_classrel_i   = extend_sign (ext_classrel false) "#";
val add_defsort      = extend_sign (ext_defsort true) "#";
val add_defsort_i    = extend_sign (ext_defsort false) "#";
val add_types        = extend_sign ext_types "#";
val add_tyabbrs      = extend_sign ext_tyabbrs "#";
val add_tyabbrs_i    = extend_sign ext_tyabbrs_i "#";
val add_arities      = extend_sign (ext_arities true) "#";
val add_arities_i    = extend_sign (ext_arities false) "#";
val add_consts       = extend_sign ext_consts "#";
val add_consts_i     = extend_sign ext_consts_i "#";
val add_syntax       = extend_sign ext_syntax "#";
val add_syntax_i     = extend_sign ext_syntax_i "#";
val add_modesyntax   = extend_sign ext_modesyntax "#";
val add_modesyntax_i = extend_sign ext_modesyntax_i "#";
val add_trfuns       = extend_sign (ext_syn Syntax.extend_trfuns) "#";
val add_trfunsT      = extend_sign (ext_syn Syntax.extend_trfunsT) "#";
val add_tokentrfuns  = extend_sign (ext_syn Syntax.extend_tokentrfuns) "#";
val add_trrules      = extend_sign (ext_syn Syntax.extend_trrules) "#";
val add_trrules_i    = extend_sign (ext_syn Syntax.extend_trrules_i) "#";
val add_path         = extend_sign ext_path "#";
val add_space        = extend_sign ext_space "#";
fun add_name name sg = extend_sign K name () sg;

val make_draft = add_name "#";



(** merge signatures **)    (*exception TERM*)

fun merge_aux (sg1, sg2) =
  if fast_subsig (sg2, sg1) then sg1
  else if fast_subsig (sg1, sg2) then sg2
  else if subsig (sg2, sg1) then sg1
  else if subsig (sg1, sg2) then sg2
  else if is_draft sg1 orelse is_draft sg2 then
    raise TERM ("Illegal merge of draft signatures", [])
  else
    (*neither is union already; must form union*)
    let
      val Sg {tsig = tsig1, const_tab = const_tab1, syn = syn1,
        path, spaces = spaces1, stamps = stamps1} = sg1;
      val Sg {tsig = tsig2, const_tab = const_tab2, syn = syn2,
        path = _, spaces = spaces2, stamps = stamps2} = sg2;


      val stamps = merge_rev_lists stamps1 stamps2;
      val _ =
        (case duplicates (stamp_names stamps) of
          [] => ()
        | dups => raise TERM ("Attempt to merge different versions of theories "
            ^ commas_quote dups, []));

      val tsig = Type.merge_tsigs (tsig1, tsig2);

      val const_tab = Symtab.merge (op =) (const_tab1, const_tab2)
        handle Symtab.DUPS cs =>
          raise TERM ("Incompatible types for constant(s) " ^ commas_quote cs, []);

      val syn = Syntax.merge_syntaxes syn1 syn2;

      val kinds = distinct (map fst (spaces1 @ spaces2));
      val spaces =
        kinds ~~
          ListPair.map NameSpace.merge
            (map (space_of spaces1) kinds, map (space_of spaces2) kinds);
    in
      Sg {tsig = tsig, const_tab = const_tab, syn = syn,
        path = path, spaces = spaces, stamps = stamps}
    end;

fun merge sgs =
  (case handle_error merge_aux sgs of
    OK sg => sg
  | Error msg => raise TERM (msg, []));



(** the Pure signature **)

val proto_pure =
  make_sign (Syntax.pure_syn, Type.tsig0, Symtab.null, ([], [])) [] "#"
  |> add_types
   (("fun", 2, NoSyn) ::
    ("prop", 0, NoSyn) ::
    ("itself", 1, NoSyn) ::
    Syntax.pure_types)
  |> add_classes_i [(NameSpace.base logicC, [])]
  |> add_defsort_i logicS
  |> add_arities_i
   [("fun", [logicS, logicS], logicS),
    ("prop", [], logicS),
    ("itself", [logicS], logicS)]
  |> add_syntax Syntax.pure_syntax
  |> add_modesyntax (("symbols", true), Syntax.pure_sym_syntax)
  |> add_trfuns Syntax.pure_trfuns
  |> add_trfunsT Syntax.pure_trfunsT
  |> add_syntax
   [("==>", "[prop, prop] => prop", Delimfix "op ==>")]
  |> add_consts
   [("==", "['a::{}, 'a] => prop", InfixrName ("==", 2)),
    ("=?=", "['a::{}, 'a] => prop", InfixrName ("=?=", 2)),
    ("==>", "[prop, prop] => prop", Mixfix ("(_/ ==> _)", [2, 1], 1)),
    ("all", "('a => prop) => prop", Binder ("!!", 0, 0)),
    ("TYPE", "'a itself", NoSyn)]
  |> add_name "ProtoPure";

val pure = proto_pure
  |> add_syntax Syntax.pure_appl_syntax
  |> add_name "Pure";

val cpure = proto_pure
  |> add_syntax Syntax.pure_applC_syntax
  |> add_name "CPure";


end;


val long_names = Sign.long_names;
