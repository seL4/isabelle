(*  Title:      Pure/sign.ML
    ID:         $Id$
    Author:     Lawrence C Paulson and Markus Wenzel

The abstract type "sg" of signatures.
*)

(*base names*)
type bstring = string;
type bclass = class;
(*external forms -- partially qualified names*)
type xstring = string;
type xclass = class;
type xsort = sort;
type xtyp = typ;
type xterm = term;

signature SIGN =
sig
  type sg
  type sg_ref
  type data
  val rep_sg: sg ->
   {self: sg_ref,
    tsig: Type.type_sig,
    const_tab: typ Symtab.table,
    syn: Syntax.syntax,
    path: string list,
    spaces: (string * NameSpace.T) list,
    data: data}
  val name_of: sg -> string
  val stamp_names_of: sg -> string list
  val tsig_of: sg -> Type.type_sig
  val deref: sg_ref -> sg
  val self_ref: sg -> sg_ref
  val subsig: sg * sg -> bool
  val eq_sg: sg * sg -> bool
  val same_sg: sg * sg -> bool
  val is_draft: sg -> bool
  val is_stale: sg -> bool
  val const_type: sg -> string -> typ option
  val classes: sg -> class list
  val defaultS: sg -> sort
  val subsort: sg -> sort * sort -> bool
  val nodup_Vars: term -> unit
  val norm_sort: sg -> sort -> sort
  val nonempty_sort: sg -> sort list -> sort -> bool
  val of_sort: sg -> typ * sort -> bool
  val long_names: bool ref
  val classK: string
  val typeK: string
  val constK: string
  val full_name: sg -> bstring -> string
  val full_name_path: sg -> string -> bstring -> string
  val base_name: string -> bstring
  val intern: sg -> string -> xstring -> string
  val extern: sg -> string -> string -> xstring
  val cond_extern: sg -> string -> string -> xstring
  val intern_class: sg -> xclass -> class
  val intern_tycon: sg -> xstring -> string
  val intern_const: sg -> xstring -> string
  val intern_sort: sg -> xsort -> sort
  val intern_typ: sg -> xtyp -> typ
  val intern_term: sg -> xterm -> term
  val intern_tycons: sg -> xtyp -> typ
  val pretty_sg: sg -> Pretty.T
  val str_of_sg: sg -> string
  val pprint_sg: sg -> pprint_args -> unit
  val pretty_term: sg -> term -> Pretty.T
  val pretty_typ: sg -> typ -> Pretty.T
  val pretty_sort: sg -> sort -> Pretty.T
  val pretty_classrel: sg -> class * class -> Pretty.T
  val pretty_arity: sg -> string * sort list * sort -> Pretty.T
  val string_of_term: sg -> term -> string
  val string_of_typ: sg -> typ -> string
  val string_of_sort: sg -> sort -> string
  val str_of_sort: sg -> sort -> string
  val str_of_classrel: sg -> class * class -> string
  val str_of_arity: sg -> string * sort list * sort -> string
  val pprint_term: sg -> term -> pprint_args -> unit
  val pprint_typ: sg -> typ -> pprint_args -> unit
  val certify_typ: sg -> typ -> typ
  val certify_term: sg -> term -> term * typ * int
  val read_raw_typ: sg * (indexname -> sort option) -> string -> typ
  val read_typ: sg * (indexname -> sort option) -> string -> typ
  val infer_types: sg -> (indexname -> typ option) ->
    (indexname -> sort option) -> string list -> bool
    -> xterm list * typ -> term * (indexname * typ) list
  val infer_types_simult: sg -> (indexname -> typ option) ->
    (indexname -> sort option) -> string list -> bool
    -> (xterm list * typ) list -> term list * (indexname * typ) list
  val add_classes: (bclass * xclass list) list -> sg -> sg
  val add_classes_i: (bclass * class list) list -> sg -> sg
  val add_classrel: (xclass * xclass) list -> sg -> sg
  val add_classrel_i: (class * class) list -> sg -> sg
  val add_defsort: xsort -> sg -> sg
  val add_defsort_i: sort -> sg -> sg
  val add_types: (bstring * int * mixfix) list -> sg -> sg
  val add_nonterminals: bstring list -> sg -> sg
  val add_tyabbrs: (bstring * string list * string * mixfix) list -> sg -> sg
  val add_tyabbrs_i: (bstring * string list * typ * mixfix) list -> sg -> sg
  val add_arities: (xstring * xsort list * xsort) list -> sg -> sg
  val add_arities_i: (string * sort list * sort) list -> sg -> sg
  val add_consts: (bstring * string * mixfix) list -> sg -> sg
  val add_consts_i: (bstring * typ * mixfix) list -> sg -> sg
  val add_syntax: (bstring * string * mixfix) list -> sg -> sg
  val add_syntax_i: (bstring * typ * mixfix) list -> sg -> sg
  val add_modesyntax: (string * bool) * (bstring * string * mixfix) list -> sg -> sg
  val add_modesyntax_i: (string * bool) * (bstring * typ * mixfix) list -> sg -> sg
  val add_trfuns:
    (string * (ast list -> ast)) list *
    (string * (term list -> term)) list *
    (string * (term list -> term)) list *
    (string * (ast list -> ast)) list -> sg -> sg
  val add_trfunsT:
    (string * (bool -> typ -> term list -> term)) list -> sg -> sg
  val add_tokentrfuns:
    (string * string * (string -> string * int)) list -> sg -> sg
  val add_trrules: (xstring * string) Syntax.trrule list -> sg -> sg
  val add_trrules_i: ast Syntax.trrule list -> sg -> sg
  val add_path: string -> sg -> sg
  val add_space: string * string list -> sg -> sg
  val add_name: string -> sg -> sg
  val data_kinds: data -> string list
  val init_data: string * (object * (object -> object) *
    (object * object -> object) * (sg -> object -> unit)) -> sg -> sg
  val get_data: sg -> string -> object
  val put_data: string * object -> sg -> sg
  val print_data: sg -> string -> unit
  val merge_refs: sg_ref * sg_ref -> sg_ref
  val merge: sg * sg -> sg
  val prep_ext: sg -> sg
  val nontriv_merge: sg * sg -> sg
  val pre_pure: sg
  val const_of_class: class -> string
  val class_of_const: string -> class
end;

structure Sign: SIGN =
struct


(** datatype sg **)

(* types sg, data, sg_ref *)

datatype sg =
  Sg of
   {id: string ref,                             (*id*)
    stamps: string ref list} *                  (*unique theory indentifier*)
   {self: sg_ref,                               (*mutable self reference*)
    tsig: Type.type_sig,                        (*order-sorted signature of types*)
    const_tab: typ Symtab.table,                (*type schemes of constants*)
    syn: Syntax.syntax,                         (*syntax for parsing and printing*)
    path: string list,                          (*current name space entry prefix*)
    spaces: (string * NameSpace.T) list,        (*name spaces for consts, types etc.*)
    data: data}                                 (*anytype data*)
and data =
  Data of
    (object *                             	(*value*)
     ((object -> object) *                	(*prepare extend method*)
      (object * object -> object) *       	(*merge and prepare extend method*)
      (sg -> object -> unit)))                 	(*print method*)
    Symtab.table
and sg_ref =
  SgRef of sg ref option

(*make signature*)
fun make_sign (id, self, tsig, const_tab, syn, path, spaces, data, stamps) =
  Sg ({id = id, stamps = stamps}, {self = self, tsig = tsig, const_tab = const_tab,
    syn = syn, path = path, spaces = spaces, data = data});


(* basic operations *)

fun rep_sg (Sg (_, args)) = args;

(*show stamps*)
fun stamp_names_of (Sg ({stamps, ...}, _)) = rev (map ! stamps);
fun pretty_sg sg = Pretty.str_list "{" "}" (stamp_names_of sg);
val str_of_sg = Pretty.str_of o pretty_sg;
val pprint_sg = Pretty.pprint o pretty_sg;

val tsig_of = #tsig o rep_sg;

fun const_type (Sg (_, {const_tab, ...})) c = Symtab.lookup (const_tab, c);


(* id and self *)

fun check_stale (sg as Sg ({id, ...},
        {self = SgRef (Some (ref (Sg ({id = id', ...}, _)))), ...})) =
      if id = id' then sg
      else raise TERM ("Stale signature: " ^ str_of_sg sg, [])
  | check_stale _ = sys_error "Sign.check_stale";

fun is_stale sg = (check_stale sg; false) handle TERM _ => true;

fun self_ref (sg as Sg (_, {self, ...})) = (check_stale sg; self);

fun deref (SgRef (Some (ref sg))) = sg
  | deref (SgRef None) = sys_error "Sign.deref";

fun name_of (sg as Sg ({id = ref name, ...}, _)) =
  if name = "" orelse ord name = ord "#" then
    raise TERM ("Nameless signature " ^ str_of_sg sg, [])
  else name;


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
  fun eq_sg (sg1 as Sg ({id = id1, ...}, _), sg2 as Sg ({id = id2, ...}, _)) =
    (check_stale sg1; check_stale sg2; id1 = id2);

  fun subsig (sg1 as Sg ({stamps = s1, ...}, _), sg2 as Sg ({stamps = s2, ...}, _)) =
    eq_sg (sg1, sg2) orelse subset_stamp (s1, s2);

  fun fast_subsig (sg1 as Sg ({stamps = s1, ...}, _), sg2 as Sg ({stamps = s2, ...}, _)) =
    eq_sg (sg1, sg2) orelse fast_sub (s1, s2);
end;


(*test if same theory names are contained in signatures' stamps,
  i.e. if signatures belong to same theory but not necessarily to the
  same version of it*)
fun same_sg (sg1 as Sg ({stamps = s1, ...}, _), sg2 as Sg ({stamps = s2, ...}, _)) =
  eq_sg (sg1, sg2) orelse eq_set_string (pairself (map (op !)) (s1, s2));

(*test for drafts*)
fun is_draft (Sg ({stamps = ref name :: _, ...}, _)) = name = "" orelse ord name = ord "#";


(* classes and sorts *)

val classes = #classes o Type.rep_tsig o tsig_of;

val defaultS = Type.defaultS o tsig_of;
val subsort = Type.subsort o tsig_of;
val norm_sort = Type.norm_sort o tsig_of;
val nonempty_sort = Type.nonempty_sort o tsig_of;

fun of_sort (Sg (_, {tsig, ...})) =
  Sorts.of_sort (#classrel (Type.rep_tsig tsig)) (#arities (Type.rep_tsig tsig));



(** signature data **)

(* errors *)

fun of_theory sg = "\nof theory " ^ str_of_sg sg;

fun err_method name kind =
  error ("Error while invoking " ^ quote kind ^ " " ^ name ^ " method");

fun err_dup_init sg kind =
  error ("Duplicate initialization of " ^ quote kind ^ " data" ^ of_theory sg);

fun err_uninit sg kind =
  error ("Tried to access uninitialized " ^ quote kind ^ " data" ^ of_theory sg);


(* prepare data *)

val empty_data = Data Symtab.empty;

fun merge_data (Data tab1, Data tab2) =
  let
    val data1 = Symtab.dest tab1;
    val data2 = Symtab.dest tab2;
    val all_data = data1 @ data2;
    val kinds = distinct (map fst all_data);

   fun entry data kind =
     (case assoc (data, kind) of
       None => []
     | Some x => [(kind, x)]);

    fun merge_entries [(kind, (e, mths as (ext, _, _)))] =
          (kind, (ext e handle _ => err_method "prep_ext" kind, mths))
      | merge_entries [(kind, (e1, mths as (_, mrg, _))), (_, (e2, _))] =
          (kind, (mrg (e1, e2) handle _ => err_method "merge" kind, mths))
      | merge_entries _ = sys_error "merge_entries";

    val data = map (fn k => merge_entries (entry data1 k @ entry data2 k)) kinds;
  in Data (Symtab.make data) end;

fun prep_ext_data data = merge_data (data, empty_data);

fun init_data_sg sg (Data tab) kind e ext mrg prt =
  Data (Symtab.update_new ((kind, (e, (ext, mrg, prt))), tab))
    handle Symtab.DUP _ => err_dup_init sg kind;


(* access data *)

fun data_kinds (Data tab) = map fst (Symtab.dest tab);

fun lookup_data sg tab kind =
  (case Symtab.lookup (tab, kind) of
    Some x => x
  | None => err_uninit sg kind);

fun get_data (sg as Sg (_, {data = Data tab, ...})) kind =
  fst (lookup_data sg tab kind);

fun print_data (sg as Sg (_, {data = Data tab, ...})) kind =
  let val (e, (_, _, prt)) = lookup_data sg tab kind
  in prt sg e handle _ => err_method ("print" ^ of_theory sg) kind end;

fun put_data_sg sg (Data tab) kind e =
  Data (Symtab.update ((kind, (e, snd (lookup_data sg tab kind))), tab));



(** build signatures **)

fun ext_stamps stamps (id as ref name) =
  let val stmps = (case stamps of ref "#" :: ss => ss | ss => ss) in
    if exists (equal name o !) stmps then
      error ("Theory already contains a " ^ quote name ^ " component")
    else id :: stmps
  end;

fun create_sign self stamps name (syn, tsig, ctab, (path, spaces), data) =
  let
    val id = ref name;
    val sign =
      make_sign (id, self, tsig, ctab, syn, path, spaces, data, ext_stamps stamps id);
  in
    (case self of
      SgRef (Some r) => r := sign
    | _ => sys_error "Sign.create_sign");
    sign
  end;

fun extend_sign keep extfun name decls
    (sg as Sg ({id = _, stamps}, {self, tsig, const_tab, syn, path, spaces, data})) =
  let
    val _ = check_stale sg;
    val (self', data') =
      if is_draft sg andalso keep then (self, data)
      else (SgRef (Some (ref sg)), prep_ext_data data);
  in
    create_sign self' stamps name
      (extfun (syn, tsig, const_tab, (path, spaces), data') decls)
  end;



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
fun intrn spaces kind = NameSpace.intern (space_of spaces kind);
fun extrn spaces kind = NameSpace.extern (space_of spaces kind);

(*add names*)
fun add_names spaces kind names =
  let val space' = NameSpace.extend (space_of spaces kind, names) in
    overwrite (spaces, (kind, space'))
  end;

(*make full names*)
fun full path name =
  if name = "" then error "Attempt to declare empty name \"\""
  else if NameSpace.qualified name then
    error ("Attempt to declare qualified name " ^ quote name)
  else NameSpace.pack (path @ [name]);

(*base name*)
val base_name = NameSpace.base;


(* intern / extern names *)

local
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

  val spaces_of = #spaces o rep_sg;
in
  fun intrn_class spaces = intrn spaces classK;
  fun extrn_class spaces = extrn spaces classK;

  val intrn_sort = map o intrn_class;
  val intrn_typ = trn_typ o intrn;
  val intrn_term = trn_term o intrn;

  val extrn_sort = map o extrn_class;
  val extrn_typ = trn_typ o extrn;
  val extrn_term = trn_term o extrn;

  fun intrn_tycons spaces T =
    map_typ I (mapping (intrn spaces typeK) add_typ_tycons T) T;

  val intern = intrn o spaces_of;
  val extern = extrn o spaces_of;
  fun cond_extern sg kind = if ! long_names then I else extern sg kind;

  val intern_class = intrn_class o spaces_of;
  val intern_sort = intrn_sort o spaces_of;
  val intern_typ = intrn_typ o spaces_of;
  val intern_term = intrn_term o spaces_of;

  fun intern_tycon sg = intrn (spaces_of sg) typeK;
  fun intern_const sg = intrn (spaces_of sg) constK;

  val intern_tycons = intrn_tycons o spaces_of;

  val full_name = full o #path o rep_sg;
  fun full_name_path sg elems name =
    full (#path (rep_sg sg) @ NameSpace.unpack elems) name;
end;



(** pretty printing of terms, types etc. **)

fun pretty_term (sg as Sg ({stamps, ...}, {syn, spaces, ...})) t =
  Syntax.pretty_term syn
    (exists (equal "CPure" o !) stamps)
    (if ! long_names then t else extrn_term spaces t);

fun pretty_typ (Sg (_, {syn, spaces, ...})) T =
  Syntax.pretty_typ syn
    (if ! long_names then T else extrn_typ spaces T);

fun pretty_sort (Sg (_, {syn, spaces, ...})) S =
  Syntax.pretty_sort syn
    (if ! long_names then S else extrn_sort spaces S);

fun pretty_classrel sg (c1, c2) = Pretty.block
  [pretty_sort sg [c1], Pretty.str " <", Pretty.brk 1, pretty_sort sg [c2]];

fun pretty_arity sg (t, Ss, S) =
  let
    val t' = cond_extern sg typeK t;
    val dom =
      if null Ss then []
      else [Pretty.list "(" ")" (map (pretty_sort sg) Ss), Pretty.brk 1];
  in
    Pretty.block
      ([Pretty.str (t' ^ " ::"), Pretty.brk 1] @ dom @ [pretty_sort sg S])
  end;

fun string_of_term sg t = Pretty.string_of (pretty_term sg t);
fun string_of_typ sg T = Pretty.string_of (pretty_typ sg T);
fun string_of_sort sg S = Pretty.string_of (pretty_sort sg S);

fun str_of_sort sg S = Pretty.str_of (pretty_sort sg S);
fun str_of_classrel sg c1_c2 = Pretty.str_of (pretty_classrel sg c1_c2);
fun str_of_arity sg ar = Pretty.str_of (pretty_arity sg ar);

fun pprint_term sg = Pretty.pprint o Pretty.quote o (pretty_term sg);
fun pprint_typ sg = Pretty.pprint o Pretty.quote o (pretty_typ sg);



(** read types **)  (*exception ERROR*)

fun err_in_type s =
  error ("The error(s) above occurred in type " ^ quote s);

fun rd_raw_typ syn tsig spaces def_sort str =
  intrn_tycons spaces
    (Syntax.read_typ syn (Type.get_sort tsig def_sort (intrn_sort spaces)) str
      handle ERROR => err_in_type str);

fun read_raw_typ (sg as Sg (_, {tsig, syn, spaces, ...}), def_sort) str =
  (check_stale sg; rd_raw_typ syn tsig spaces def_sort str);

(*read and certify typ wrt a signature*)
fun read_typ (sg, def_sort) str =
  (Type.cert_typ (tsig_of sg) (read_raw_typ (sg, def_sort) str)
      handle TYPE (msg, _, _) => (error_msg msg; err_in_type str));



(** certify types and terms **)   (*exception TYPE*)

(* certify_typ *)

val certify_typ = Type.cert_typ o tsig_of;


(* certify_term *)

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

(*compute and check type of the term*)
fun type_check sg tm =
  let
    val prt =
      setmp Syntax.show_brackets true
        (setmp long_names true (pretty_term sg));
    val prT = setmp long_names true (pretty_typ sg);

    fun err_appl why bs t T u U =
      let
        val xs = map Free bs;		(*we do not rename here*)
        val t' = subst_bounds (xs, t);
        val u' = subst_bounds (xs, u);
        val text = cat_lines
         ["Type error in application: " ^ why,
          "",
          Pretty.string_of (Pretty.block [Pretty.str "Operator:", Pretty.brk 2, prt t',
            Pretty.str " :: ", prT T]),
          Pretty.string_of (Pretty.block [Pretty.str "Operand:", Pretty.brk 3, prt u',
            Pretty.str " :: ", prT U]), ""];
      in raise TYPE (text, [T, U], [t', u']) end;

    fun typ_of (_, Const (_, T)) = T
      | typ_of (_, Free  (_, T)) = T
      | typ_of (_, Var (_, T)) = T
      | typ_of (bs, Bound i) = snd (nth_elem (i, bs) handle LIST _ =>
          raise TYPE ("Loose bound variable: B." ^ string_of_int i, [], [Bound i]))
      | typ_of (bs, Abs (x, T, body)) = T --> typ_of ((x, T) :: bs, body)
      | typ_of (bs, t $ u) =
          let val T = typ_of (bs, t) and U = typ_of (bs, u) in
            (case T of
              Type ("fun", [T1, T2]) =>
                if T1 = U then T2 else err_appl "Incompatible operand type." bs t T u U
            | _ => err_appl "Operator not of function type." bs t T u U)
          end;

  in typ_of ([], tm) end;


fun certify_term sg tm =
  let
    val _ = check_stale sg;
    val tsig = tsig_of sg;

    fun show_const a T = quote a ^ " :: " ^ quote (string_of_typ sg T);

    fun atom_err (errs, Const (a, T)) =
        (case const_type sg a of
          None => ("Undeclared constant " ^ show_const a T) :: errs
        | Some U =>
            if Type.typ_instance (tsig, T, U) then errs
            else ("Illegal type for constant " ^ show_const a T) :: errs)
      | atom_err (errs, Var ((x, i), _)) =
          if i < 0 then ("Negative index for Var " ^ quote x) :: errs else errs
      | atom_err (errs, _) = errs;

    val norm_tm =
      (case it_term_types (Type.typ_errors tsig) (tm, []) of
        [] => map_term_types (Type.norm_typ tsig) tm
      | errs => raise TYPE (cat_lines errs, [], [tm]));
    val _ = nodup_Vars norm_tm;
  in
    (case foldl_aterms atom_err ([], norm_tm) of
      [] => (norm_tm, type_check sg norm_tm, maxidx_of_term norm_tm)
    | errs => raise TYPE (cat_lines errs, [], [norm_tm]))
  end;



(** infer_types **)         (*exception ERROR*)

(*
  def_type: partial map from indexnames to types (constrains Frees, Vars)
  def_sort: partial map from indexnames to sorts (constrains TFrees, TVars)
  used: list of already used type variables
  freeze: if true then generated parameters are turned into TFrees, else TVars

  termss: lists of alternative parses (only one combination should be type-correct)
  typs: expected types
*)

fun infer_types_simult sg def_type def_sort used freeze args =
  let
    val tsig = tsig_of sg;
    val prt =
      setmp Syntax.show_brackets true
        (setmp long_names true (pretty_term sg));
    val prT = setmp long_names true (pretty_typ sg);

    val termss = foldr multiply (map fst args, [[]]);
    val typs =
      map (fn (_, T) => certify_typ sg T handle TYPE (msg, _, _) => error msg) args;

    fun infer ts = OK
      (Type.infer_types prt prT tsig (const_type sg) def_type def_sort
        (intern_const sg) (intern_tycons sg) (intern_sort sg) used freeze typs ts)
      handle TYPE (msg, _, _) => Error msg;

    val err_results = map infer termss;
    val errs = mapfilter get_error err_results;
    val results = mapfilter get_ok err_results;

    val ambiguity = length termss;	(* FIXME !? *)
    (* FIXME to syntax.ML!? *)
    fun ambig_msg () =
      if ambiguity > 1 andalso ambiguity <= ! Syntax.ambiguity_level
      then
        error_msg "Got more than one parse tree.\n\
          \Retry with smaller Syntax.ambiguity_level for more information."
      else ();
  in
    if null results then (ambig_msg (); error (cat_lines errs))
    else if length results = 1 then
      (if ambiguity > ! Syntax.ambiguity_level then
        warning "Fortunately, only one parse tree is type correct.\n\
          \You may still want to disambiguate your grammar or your input."
      else (); hd results)
    else (ambig_msg (); error ("More than one term is type correct:\n" ^
      (cat_lines (map (Pretty.string_of o prt) (flat (map fst results))))))
  end;


fun infer_types sg def_type def_sort used freeze tsT =
  apfst hd (infer_types_simult sg def_type def_sort used freeze [tsT]);



(** extend signature **)    (*exception ERROR*)

(** signature extension functions **)  (*exception ERROR*)

fun decls_of path name_of mfixs =
  map (fn (x, y, mx) => (full path (name_of x mx), y)) mfixs;

fun no_read _ _ _ decl = decl;


(* add default sort *)

fun ext_defsort int (syn, tsig, ctab, (path, spaces), data) S =
  (syn, Type.ext_tsig_defsort tsig (if int then intrn_sort spaces S else S),
    ctab, (path, spaces), data);


(* add type constructors *)

fun ext_types (syn, tsig, ctab, (path, spaces), data) types =
  let val decls = decls_of path Syntax.type_name types in
    (Syntax.extend_type_gram syn types,
      Type.ext_tsig_types tsig decls, ctab,
      (path, add_names spaces typeK (map fst decls)), data)
  end;

fun ext_nonterminals sg nonterms =
  ext_types sg (map (fn n => (n, 0, Syntax.NoSyn)) nonterms);


(* add type abbreviations *)

fun read_abbr syn tsig spaces (t, vs, rhs_src) =
  (t, vs, rd_raw_typ syn tsig spaces (K None) rhs_src)
    handle ERROR => error ("in type abbreviation " ^ t);

fun ext_abbrs rd_abbr (syn, tsig, ctab, (path, spaces), data) abbrs =
  let
    fun mfix_of (t, vs, _, mx) = (t, length vs, mx);
    val syn' = Syntax.extend_type_gram syn (map mfix_of abbrs);

    val abbrs' =
      map (fn (t, vs, rhs, mx) =>
        (full path (Syntax.type_name t mx), vs, rhs)) abbrs;
    val spaces' = add_names spaces typeK (map #1 abbrs');
    val decls = map (rd_abbr syn' tsig spaces') abbrs';
  in
    (syn', Type.ext_tsig_abbrs tsig decls, ctab, (path, spaces'), data)
  end;

fun ext_tyabbrs abbrs = ext_abbrs read_abbr abbrs;
fun ext_tyabbrs_i abbrs = ext_abbrs no_read abbrs;


(* add type arities *)

fun ext_arities int (syn, tsig, ctab, (path, spaces), data) arities =
  let
    fun intrn_arity (c, Ss, S) =
      (intrn spaces typeK c, map (intrn_sort spaces) Ss, intrn_sort spaces S);
    val intrn = if int then map intrn_arity else I;
    val tsig' = Type.ext_tsig_arities tsig (intrn arities);
    val log_types = Type.logical_types tsig';
  in
    (Syntax.extend_log_types syn log_types, tsig', ctab, (path, spaces), data)
  end;


(* add term constants and syntax *)

fun const_name path c mx =
  full path (Syntax.const_name c mx);

fun err_in_const c =
  error ("in declaration of constant " ^ quote c);

fun err_dup_consts cs =
  error ("Duplicate declaration of constant(s) " ^ commas_quote cs);


fun read_const syn tsig (path, spaces) (c, ty_src, mx) =
  (c, rd_raw_typ syn tsig spaces (K None) ty_src, mx)
    handle ERROR => err_in_const (const_name path c mx);

fun ext_cnsts rd_const syn_only prmode (syn, tsig, ctab, (path, spaces), data) raw_consts =
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
      Symtab.extend (ctab, decls)
        handle Symtab.DUPS cs => err_dup_consts cs,
      (path, add_names spaces constK (map fst decls)), data)
  end;

fun ext_consts_i sg = ext_cnsts no_read false ("", true) sg;
fun ext_consts sg = ext_cnsts read_const false ("", true) sg;
fun ext_syntax_i sg = ext_cnsts no_read true ("", true) sg;
fun ext_syntax sg = ext_cnsts read_const true ("", true) sg;
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


fun ext_classes int (syn, tsig, ctab, (path, spaces), data) classes =
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
        Type.ext_tsig_classes tsig classes', ctab, (path, spaces'), data)
    consts
  end;


(* add to classrel *)

fun ext_classrel int (syn, tsig, ctab, (path, spaces), data) pairs =
  let val intrn = if int then map (pairself (intrn_class spaces)) else I in
    (syn, Type.ext_tsig_classrel tsig (intrn pairs), ctab, (path, spaces), data)
  end;


(* add translation rules *)

fun ext_trrules (syn, tsig, ctab, (path, spaces), data) args =
  (Syntax.extend_trrules syn
    (map (Syntax.map_trrule (fn (root, str) => (intrn spaces typeK root, str))) args),
      tsig, ctab, (path, spaces), data);


(* add to syntax *)

fun ext_syn extfun (syn, tsig, ctab, names, data) args =
  (extfun syn args, tsig, ctab, names, data);


(* add to path *)

fun ext_path (syn, tsig, ctab, (path, spaces), data) elems =
  let
    val path' =
      if elems = ".." andalso not (null path) then fst (split_last path)
      else if elems = "/" then []
      else path @ NameSpace.unpack elems;
  in
    (syn, tsig, ctab, (path', spaces), data)
  end;      


(* add to name space *)

fun ext_space (syn, tsig, ctab, (path, spaces), data) (kind, names) =
  (syn, tsig, ctab, (path, add_names spaces kind names), data);


(* signature data *)

fun ext_init_data sg (syn, tsig, ctab, names, data) (kind, (e, ext, mrg, prt)) =
  (syn, tsig, ctab, names, init_data_sg sg data kind e ext mrg prt);

fun ext_put_data sg (syn, tsig, ctab, names, data) (kind, e) =
  (syn, tsig, ctab, names, put_data_sg sg data kind e);


(* the external interfaces *)

val add_classes      = extend_sign true (ext_classes true) "#";
val add_classes_i    = extend_sign true (ext_classes false) "#";
val add_classrel     = extend_sign true (ext_classrel true) "#";
val add_classrel_i   = extend_sign true (ext_classrel false) "#";
val add_defsort      = extend_sign true (ext_defsort true) "#";
val add_defsort_i    = extend_sign true (ext_defsort false) "#";
val add_types        = extend_sign true ext_types "#";
val add_nonterminals = extend_sign true ext_nonterminals "#";
val add_tyabbrs      = extend_sign true ext_tyabbrs "#";
val add_tyabbrs_i    = extend_sign true ext_tyabbrs_i "#";
val add_arities      = extend_sign true (ext_arities true) "#";
val add_arities_i    = extend_sign true (ext_arities false) "#";
val add_consts       = extend_sign true ext_consts "#";
val add_consts_i     = extend_sign true ext_consts_i "#";
val add_syntax       = extend_sign true ext_syntax "#";
val add_syntax_i     = extend_sign true ext_syntax_i "#";
val add_modesyntax   = extend_sign true ext_modesyntax "#";
val add_modesyntax_i = extend_sign true ext_modesyntax_i "#";
val add_trfuns       = extend_sign true (ext_syn Syntax.extend_trfuns) "#";
val add_trfunsT      = extend_sign true (ext_syn Syntax.extend_trfunsT) "#";
val add_tokentrfuns  = extend_sign true (ext_syn Syntax.extend_tokentrfuns) "#";
val add_trrules      = extend_sign true ext_trrules "#";
val add_trrules_i    = extend_sign true (ext_syn Syntax.extend_trrules_i) "#";
val add_path         = extend_sign true ext_path "#";
val add_space        = extend_sign true ext_space "#";
fun init_data arg sg = extend_sign true (ext_init_data sg) "#" arg sg;
fun put_data arg sg  = extend_sign true (ext_put_data sg) "#" arg sg;
fun add_name name sg = extend_sign true K name () sg;
fun prep_ext sg      = extend_sign false K "#" () sg;



(** merge signatures **)    	(*exception TERM*)

(* merge_stamps *)

fun merge_stamps stamps1 stamps2 =
  let val stamps = merge_rev_lists stamps1 stamps2 in
    (case duplicates (map ! stamps) of
      [] => stamps
    | dups => raise TERM ("Attempt to merge different versions of theories "
        ^ commas_quote dups, []))
  end;


(* implicit merge -- trivial only *)

fun merge_refs (sgr1 as SgRef (Some (ref (sg1 as Sg ({stamps = s1, ...}, _)))),
        sgr2 as SgRef (Some (ref (sg2 as Sg ({stamps = s2, ...}, _))))) =
      if fast_subsig (sg2, sg1) then sgr1
      else if fast_subsig (sg1, sg2) then sgr2
      else if subsig (sg2, sg1) then sgr1
      else if subsig (sg1, sg2) then sgr2
      else (merge_stamps s1 s2; (*check for different versions*)
        raise TERM ("Attempt to do non-trivial merge of signatures", []))
  | merge_refs _ = sys_error "Sign.merge_refs";

val merge = deref o merge_refs o pairself self_ref;


(* proper merge *)

fun merge_aux (sg1, sg2) =
  if subsig (sg2, sg1) then sg1
  else if subsig (sg1, sg2) then sg2
  else if is_draft sg1 orelse is_draft sg2 then
    raise TERM ("Attempt to merge draft signatures", [])
  else
    (*neither is union already; must form union*)
    let
      val Sg ({id = _, stamps = stamps1}, {self = _, tsig = tsig1, const_tab = const_tab1,
        syn = syn1, path = _, spaces = spaces1, data = data1}) = sg1;
      val Sg ({id = _, stamps = stamps2}, {self = _, tsig = tsig2, const_tab = const_tab2,
        syn = syn2, path = _, spaces = spaces2, data = data2}) = sg2;

      val id = ref "";
      val self_ref = ref sg1;                   (*dummy value*)
      val self = SgRef (Some self_ref);

      val stamps = merge_stamps stamps1 stamps2;
      val tsig = Type.merge_tsigs (tsig1, tsig2);
      val const_tab = Symtab.merge (op =) (const_tab1, const_tab2)
        handle Symtab.DUPS cs =>
          raise TERM ("Incompatible types for constant(s) " ^ commas_quote cs, []);
      val syn = Syntax.merge_syntaxes syn1 syn2;

      val path = [];
      val kinds = distinct (map fst (spaces1 @ spaces2));
      val spaces =
        kinds ~~
          ListPair.map NameSpace.merge
            (map (space_of spaces1) kinds, map (space_of spaces2) kinds);

      val data = merge_data (data1, data2);

      val sign = make_sign (id, self, tsig, const_tab, syn, path, spaces, data, stamps);
    in
      self_ref := sign; sign
    end;

fun nontriv_merge sg1_sg2 =
  (case handle_error merge_aux sg1_sg2 of
    OK sg => sg
  | Error msg => raise TERM (msg, []));



(** partial Pure signature **)

val dummy_sg = make_sign (ref "", SgRef None, Type.tsig0,
  Symtab.empty, Syntax.pure_syn, [], [], empty_data, []);

val pre_pure =
  create_sign (SgRef (Some (ref dummy_sg))) [] "#"
    (Syntax.pure_syn, Type.tsig0, Symtab.empty, ([], []), empty_data);


end;


val long_names = Sign.long_names;
