(*  Title:      Pure/sign.ML
    ID:         $Id$
    Author:     Lawrence C Paulson and Markus Wenzel

The abstract type "sg" of signatures.
*)

signature SIGN =
sig
  type sg
  type sg_ref
  type data
  val rep_sg: sg ->
   {self: sg_ref,
    tsig: Type.tsig,
    consts: (typ * stamp) NameSpace.table,
    naming: NameSpace.naming,
    data: data}
  val stamp_names_of: sg -> string list
  val exists_stamp: string -> sg -> bool
  val pretty_sg: sg -> Pretty.T
  val pprint_sg: sg -> pprint_args -> unit
  val pretty_abbrev_sg: sg -> Pretty.T
  val str_of_sg: sg -> string
  val is_stale: sg -> bool
  val self_ref: sg -> sg_ref
  val deref: sg_ref -> sg
  val name_of: sg -> string
  val is_draft: sg -> bool
  val eq_sg: sg * sg -> bool
  val subsig: sg * sg -> bool
  val same_sg: sg * sg -> bool
  val joinable: sg * sg -> bool
  val prep_ext: sg -> sg
  val copy: sg -> sg
  val add_name: string -> sg -> sg
  val data_kinds: data -> string list
  val print_all_data: sg -> unit
  val pre_pure: sg
  val PureN: string
  val CPureN: string
  val naming_of: sg -> NameSpace.naming
  val base_name: string -> bstring
  val full_name: sg -> bstring -> string
  val full_name_path: sg -> string -> bstring -> string
  val declare_name: sg -> string -> NameSpace.T -> NameSpace.T
  val syn_of: sg -> Syntax.syntax
  val tsig_of: sg -> Type.tsig
  val classes: sg -> class list
  val defaultS: sg -> sort
  val subsort: sg -> sort * sort -> bool
  val of_sort: sg -> typ * sort -> bool
  val witness_sorts: sg -> sort list -> sort list -> (typ * sort) list
  val universal_witness: sg -> (typ * sort) option
  val typ_instance: sg -> typ * typ -> bool
  val is_logtype: sg -> string -> bool
  val const_type: sg -> string -> typ option
  val the_const_type: sg -> string -> typ
  val declared_tyname: sg -> string -> bool
  val declared_const: sg -> string -> bool
  val class_space: sg -> NameSpace.T
  val type_space: sg -> NameSpace.T
  val const_space: sg -> NameSpace.T
  val intern_class: sg -> xstring -> string
  val extern_class: sg -> string -> xstring
  val intern_type: sg -> xstring -> string
  val extern_type: sg -> string -> xstring
  val intern_const: sg -> xstring -> string
  val extern_const: sg -> string -> xstring
  val intern_sort: sg -> sort -> sort
  val extern_sort: sg -> sort -> sort
  val intern_typ: sg -> typ -> typ
  val extern_typ: sg -> typ -> typ
  val intern_term: sg -> term -> term
  val extern_term: sg -> term -> term
  val intern_tycons: sg -> typ -> typ
  val pretty_term': Syntax.syntax -> sg -> term -> Pretty.T
  val pretty_term: sg -> term -> Pretty.T
  val pretty_typ: sg -> typ -> Pretty.T
  val pretty_sort: sg -> sort -> Pretty.T
  val pretty_classrel: sg -> class list -> Pretty.T
  val pretty_arity: sg -> arity -> Pretty.T
  val string_of_term: sg -> term -> string
  val string_of_typ: sg -> typ -> string
  val string_of_sort: sg -> sort -> string
  val string_of_classrel: sg -> class list -> string
  val string_of_arity: sg -> arity -> string
  val pprint_term: sg -> term -> pprint_args -> unit
  val pprint_typ: sg -> typ -> pprint_args -> unit
  val pp: sg -> Pretty.pp
  val certify_class: sg -> class -> class
  val certify_sort: sg -> sort -> sort
  val certify_typ: sg -> typ -> typ
  val certify_typ_syntax: sg -> typ -> typ
  val certify_typ_abbrev: sg -> typ -> typ
  val certify_term: Pretty.pp -> sg -> term -> term * typ * int
  val read_sort': Syntax.syntax -> sg -> string -> sort
  val read_sort: sg -> string -> sort
  val read_typ': Syntax.syntax -> sg * (indexname -> sort option) -> string -> typ
  val read_typ_syntax': Syntax.syntax -> sg * (indexname -> sort option) -> string -> typ
  val read_typ_abbrev': Syntax.syntax -> sg * (indexname -> sort option) -> string -> typ
  val read_typ: sg * (indexname -> sort option) -> string -> typ
  val read_typ_syntax: sg * (indexname -> sort option) -> string -> typ
  val read_typ_abbrev: sg * (indexname -> sort option) -> string -> typ
  val read_tyname: sg -> string -> typ
  val read_const: sg -> string -> term
  val infer_types_simult: Pretty.pp -> sg -> (indexname -> typ option) ->
    (indexname -> sort option) -> string list -> bool
    -> (term list * typ) list -> term list * (indexname * typ) list
  val infer_types: Pretty.pp -> sg -> (indexname -> typ option) ->
    (indexname -> sort option) -> string list -> bool
    -> term list * typ -> term * (indexname * typ) list
  val read_def_terms': Pretty.pp -> (string -> bool) -> Syntax.syntax ->
    sg * (indexname -> typ option) * (indexname -> sort option) ->
    string list -> bool -> (string * typ) list -> term list * (indexname * typ) list
  val read_def_terms:
    sg * (indexname -> typ option) * (indexname -> sort option) ->
    string list -> bool -> (string * typ) list -> term list * (indexname * typ) list
  val simple_read_term: sg -> typ -> string -> term
  val add_defsort: string -> sg -> sg
  val add_defsort_i: sort -> sg -> sg
  val add_types: (bstring * int * mixfix) list -> sg -> sg
  val add_nonterminals: bstring list -> sg -> sg
  val add_tyabbrs: (bstring * string list * string * mixfix) list -> sg -> sg
  val add_tyabbrs_i: (bstring * string list * typ * mixfix) list -> sg -> sg
  val add_arities: (xstring * string list * string) list -> sg -> sg
  val add_arities_i: (string * sort list * sort) list -> sg -> sg
  val add_syntax: (bstring * string * mixfix) list -> sg -> sg
  val add_syntax_i: (bstring * typ * mixfix) list -> sg -> sg
  val add_modesyntax: (string * bool) * (bstring * string * mixfix) list -> sg -> sg
  val add_modesyntax_i: (string * bool) * (bstring * typ * mixfix) list -> sg -> sg
  val del_modesyntax: (string * bool) * (bstring * string * mixfix) list -> sg -> sg
  val del_modesyntax_i: (string * bool) * (bstring * typ * mixfix) list -> sg -> sg
  val add_consts: (bstring * string * mixfix) list -> sg -> sg
  val add_consts_i: (bstring * typ * mixfix) list -> sg -> sg
  val const_of_class: class -> string
  val class_of_const: string -> class
  val add_classes: (bstring * xstring list) list -> sg -> sg
  val add_classes_i: (bstring * class list) list -> sg -> sg
  val add_classrel: (xstring * xstring) list -> sg -> sg
  val add_classrel_i: (class * class) list -> sg -> sg
  val add_trfuns:
    (string * (ast list -> ast)) list *
    (string * (term list -> term)) list *
    (string * (term list -> term)) list *
    (string * (ast list -> ast)) list -> sg -> sg
  val add_trfunsT:
    (string * (bool -> typ -> term list -> term)) list -> sg -> sg
  val add_advanced_trfuns:
    (string * (sg -> ast list -> ast)) list *
    (string * (sg -> term list -> term)) list *
    (string * (sg -> term list -> term)) list *
    (string * (sg -> ast list -> ast)) list -> sg -> sg
  val add_advanced_trfunsT:
    (string * (sg -> bool -> typ -> term list -> term)) list -> sg -> sg
  val add_tokentrfuns:
    (string * string * (string -> string * real)) list -> sg -> sg
  val add_trrules: (xstring * string) Syntax.trrule list -> sg -> sg
  val add_trrules_i: ast Syntax.trrule list -> sg -> sg
  val add_path: string -> sg -> sg
  val qualified_names: sg -> sg
  val no_base_names: sg -> sg
  val custom_accesses: (string list -> string list list) -> sg -> sg
  val set_policy: (string -> bstring -> string) * (string list -> string list list) -> sg -> sg
  val restore_naming: sg -> sg -> sg
  val hide_classes: bool -> xstring list -> sg -> sg
  val hide_classes_i: bool -> string list -> sg -> sg
  val hide_types: bool -> xstring list -> sg -> sg
  val hide_types_i: bool -> string list -> sg -> sg
  val hide_consts: bool -> xstring list -> sg -> sg
  val hide_consts_i: bool -> string list -> sg -> sg
  val merge_refs: sg_ref * sg_ref -> sg_ref
  val merge: sg * sg -> sg
  val prep_ext_merge: sg list -> sg
end;

signature PRIVATE_SIGN =
sig
  include SIGN
  val init_data: Object.kind * (Object.T * (Object.T -> Object.T) * (Object.T -> Object.T) *
    (Object.T * Object.T -> Object.T) * (sg -> Object.T -> unit)) -> sg -> sg
  val get_data: Object.kind -> (Object.T -> 'a) -> sg -> 'a
  val put_data: Object.kind -> ('a -> Object.T) -> 'a -> sg -> sg
  val print_data: Object.kind -> sg -> unit
end;

structure Sign: PRIVATE_SIGN =
struct

(** datatype sg **)

(* types sg, data, syn, sg_ref *)

datatype sg =
  Sg of
   {id: string ref,
    stamps: string ref list,                  (*unique theory indentifier*)
    syn: syn} *                               (*syntax for parsing and printing*)
   {self: sg_ref,                             (*mutable self reference*)
    tsig: Type.tsig,                          (*order-sorted signature of types*)
    consts: (typ * stamp) NameSpace.table,    (*type schemes of constants*)
    naming: NameSpace.naming,
    data: data}
and data =
  Data of
    (Object.kind *                                (*kind (for authorization)*)
      (Object.T *                                 (*value*)
        ((Object.T -> Object.T) *                 (*copy method*)
          (Object.T -> Object.T) *                (*prepare extend method*)
          (Object.T * Object.T -> Object.T) *     (*merge and prepare extend method*)
          (sg -> Object.T -> unit))))             (*print method*)
    Symtab.table
and syn =
  Syn of
    Syntax.syntax *
     (((sg -> ast list -> ast) * stamp) Symtab.table *
      ((sg -> term list -> term) * stamp) Symtab.table *
      ((sg -> bool -> typ -> term list -> term) * stamp) list Symtab.table *
      ((sg -> ast list -> ast) * stamp) list Symtab.table)
and sg_ref =
  SgRef of sg ref option;

(* FIXME assign!??? *)
fun make_sg (id, self, stamps) naming data (syn, tsig, consts) =
  Sg ({id = id, stamps = stamps, syn = syn}, {self = self, tsig = tsig,
    consts = consts, naming = naming, data = data});

fun rep_sg (Sg (_, args)) = args;


(* stamps *)

fun stamps_of (Sg ({stamps, ...}, _)) = stamps;
val stamp_names_of = rev o map ! o stamps_of;
fun exists_stamp name = exists (equal name o !) o stamps_of;

fun is_stale (Sg ({id, ...}, {self = SgRef (SOME (ref (Sg ({id = id', ...}, _)))), ...})) =
      id <> id'
  | is_stale _ = false;

fun pretty_sg sg =
  Pretty.str_list "{" "}" (stamp_names_of sg @ (if is_stale sg then ["!"] else []));

val pprint_sg = Pretty.pprint o pretty_sg;

fun pretty_abbrev_sg sg =
  let
    val stamps = map ! (stamps_of sg);
    val abbrev = if length stamps > 5 then "..." :: rev (List.take (stamps, 5)) else rev stamps;
  in Pretty.str_list "{" "}" abbrev end;

val str_of_sg = Pretty.str_of o pretty_abbrev_sg;


(* id and self *)

fun check_stale pos sg =
  if is_stale sg then raise TERM ("Stale signature (in " ^ pos ^ "): " ^ str_of_sg sg, [])
  else sg;

fun self_ref (sg as Sg (_, {self, ...})) = (check_stale "Sign.self_ref" sg; self);

fun deref (SgRef (SOME (ref sg))) = sg
  | deref (SgRef NONE) = sys_error "Sign.deref";

fun assign (SgRef (SOME r)) sg = r := sg
  | assign (SgRef NONE) _ = sys_error "Sign.assign";

fun name_of (sg as Sg ({id = ref name, ...}, _)) =
  if name = "" orelse ord name = ord "#" then
    raise TERM ("Nameless signature " ^ str_of_sg sg, [])
  else name;

fun is_draft (Sg ({stamps = ref name :: _, ...}, _)) =
      name = "" orelse ord name = ord "#"
  | is_draft _ = sys_error "Sign.is_draft";


(* inclusion and equality *)

local
  (*avoiding polymorphic equality: factor 10 speedup*)
  fun mem_stamp (_: string ref, []) = false
    | mem_stamp (x, y :: ys) = x = y orelse mem_stamp (x, ys);

  fun subset_stamp ([], ys) = true
    | subset_stamp (x :: xs, ys) =
        mem_stamp (x, ys) andalso subset_stamp (xs, ys);
in
  fun eq_sg (sg1 as Sg ({id = id1, ...}, _), sg2 as Sg ({id = id2, ...}, _)) =
    (check_stale "Sign.eq_sg" sg1; check_stale "Sign.eq_sg" sg2; id1 = id2);

  fun subsig (sg1, sg2) =
    eq_sg (sg1, sg2) orelse mem_stamp (hd (stamps_of sg1), stamps_of sg2);

  fun subsig_internal (sg1, sg2) =
    eq_sg (sg1, sg2) orelse subset_stamp (stamps_of sg1, stamps_of sg2);
end;


fun joinable (sg1, sg2) = subsig (sg1, sg2) orelse subsig (sg2, sg1);

(*test if same theory names are contained in signatures' stamps,
  i.e. if signatures belong to same theory but not necessarily to the
  same version of it*)
fun same_sg (sg1, sg2) =
  eq_sg (sg1, sg2) orelse eq_set_string (pairself (map ! o stamps_of) (sg1, sg2));


(* data operations *)

fun err_method name kind e =    (* FIXME wrap exn msg!? *)
  (warning ("Error while invoking " ^ quote kind ^ " " ^ name ^ " method"); raise e);

fun err_inconsistent kinds =
  error ("Attempt to merge different versions of " ^ commas_quote kinds ^ " data");

val empty_data = Data Symtab.empty;

fun merge_data (Data tab1, Data tab2) =
  let
    val data1 = map snd (Symtab.dest tab1);
    val data2 = map snd (Symtab.dest tab2);
    val all_data = data1 @ data2;
    val kinds = gen_distinct Object.eq_kind (map fst all_data);

   fun entry data kind =
     (case gen_assoc Object.eq_kind (data, kind) of
       NONE => []
     | SOME x => [(kind, x)]);

    fun merge_entries [(kind, (e, mths as (_, ext, _, _)))] =
          (kind, (ext e handle exn => err_method "prep_ext" (Object.name_of_kind kind) exn, mths))
      | merge_entries [(kind, (e1, mths as (_, _, mrg, _))), (_, (e2, _))] =
          (kind, (mrg (e1, e2)
            handle exn => err_method "merge" (Object.name_of_kind kind) exn, mths))
      | merge_entries _ = sys_error "merge_entries";

    val data = map (fn k => merge_entries (entry data1 k @ entry data2 k)) kinds;
    val data_idx = map (fn (k, x) => (Object.name_of_kind k, (k, x))) data;
  in
    Data (Symtab.make data_idx)
      handle Symtab.DUPS dups => err_inconsistent dups
  end;

fun prep_ext_data data = merge_data (data, empty_data);

fun copy_data (Data tab) =
  let
    fun cp_data (k, (e, mths as (cp, _, _, _))) =
      (k, (cp e handle exn => err_method "copy" (Object.name_of_kind k) exn, mths));
  in Data (Symtab.map cp_data tab) end;



(** build signatures **)

fun create_sg name self stamps naming data sign =
  let
    val id = ref name;
    val stamps' = (case stamps of ref "#" :: ss => ss | ss => ss);
    val _ = conditional (exists (equal name o !) stamps')
      (fn () => error ("Theory already contains a " ^ quote name ^ " component"));
    val sg = make_sg (id, self, id :: stamps') naming data sign;
  in assign self sg; sg end;

fun new_sg f (sg as Sg ({stamps, syn, ...}, {self = _, tsig, consts, naming, data})) =
  let
    val _ = check_stale "Sign.new_sg" sg;
    val self' = SgRef (SOME (ref sg));
    val data' = f data;
  in create_sg "#" self' stamps naming data' (syn, tsig, consts) end;

val prep_ext = new_sg prep_ext_data;
val copy = new_sg copy_data;

fun add_name name (sg as Sg ({stamps, syn, ...}, {self, tsig, consts, naming, data})) =
  let
    val _ = check_stale "Sign.add_name" sg;
    val (self', data') =
      if is_draft sg then (self, data)
      else (SgRef (SOME (ref sg)), prep_ext_data data);
  in create_sg name self' stamps naming data' (syn, tsig, consts) end;

fun map_sg keep f (sg as Sg ({stamps, syn, ...}, {self, tsig, consts, naming, data})) =
  let
    val _ = check_stale "Sign.map_sg" sg;
    val (self', data') =
      if is_draft sg andalso keep then (self, data)
      else (SgRef (SOME (ref sg)), prep_ext_data data);
    val (naming', data', sign') = f (naming, data', (syn, tsig, consts));
  in create_sg "#" self' stamps naming' data' sign' end;

fun map_naming f = map_sg true (fn (naming, data, sign) => (f naming, data, sign));
fun map_data f = map_sg true (fn (naming, data, sign) => (naming, f data, sign));
fun map_sign f = map_sg true (fn (naming, data, sign) => (naming, data, f sign));
fun map_syn f = map_sign (fn (syn, tsig, consts) => (f syn, tsig, consts));
fun map_tsig f = map_sign (fn (syn, tsig, consts) => (syn, f tsig, consts));
fun map_consts f = map_sign (fn (syn, tsig, consts) => (syn, tsig, f consts));



(** signature data **)

(* errors *)

fun of_theory sg = "\nof theory " ^ str_of_sg sg;

fun err_dup_init sg kind =
  error ("Duplicate initialization of " ^ quote kind ^ " data" ^ of_theory sg);

fun err_uninit sg kind =
  error ("Tried to access uninitialized " ^ quote kind ^ " data" ^ of_theory sg);

fun err_access sg kind =
  error ("Unauthorized access to " ^ quote kind ^ " data" ^ of_theory sg);


(* access data *)

fun data_kinds (Data tab) = Symtab.keys tab;

fun lookup_data sg tab kind =
  let val name = Object.name_of_kind kind in
    (case Symtab.lookup (tab, name) of
      SOME (k, x) =>
        if Object.eq_kind (kind, k) then x
        else err_access sg name
    | NONE => err_uninit sg name)
  end;

fun init_data (kind, (e, cp, ext, mrg, prt)) sg = sg |> map_data (fn Data tab =>
  Data (Symtab.update_new ((Object.name_of_kind kind, (kind, (e, (cp, ext, mrg, prt)))), tab))
    handle Symtab.DUP name => err_dup_init sg name);

fun get_data kind dest (sg as Sg (_, {data = Data tab, ...})) =
  let val x = fst (lookup_data sg tab kind)
  in dest x handle Match => Object.kind_error kind end;

fun put_data kind mk x sg = sg |> map_data (fn Data tab =>
  Data (Symtab.update ((Object.name_of_kind kind,
    (kind, (mk x, snd (lookup_data sg tab kind)))), tab)));

fun print_data kind (sg as Sg (_, {data = Data tab, ...})) =
  let val (e, (_, _, _, prt)) = lookup_data sg tab kind in
    prt sg e handle exn =>
      err_method ("print" ^ of_theory sg) (Object.name_of_kind kind) exn
  end;

fun print_all_data (sg as Sg (_, {data = Data tab, ...})) =
  List.app (fn kind => print_data kind sg) (map (#1 o #2) (Symtab.dest tab));



(** primitive signatures **)

val pure_syn =
  Syn (Syntax.pure_syn, (Symtab.empty, Symtab.empty, Symtab.empty, Symtab.empty));

val dummy_sg = make_sg (ref "", SgRef NONE, []) NameSpace.default_naming empty_data
  (pure_syn, Type.empty_tsig, NameSpace.empty_table);

val pre_pure =
  create_sg "#" (SgRef (SOME (ref dummy_sg))) [] NameSpace.default_naming empty_data
    (pure_syn, Type.empty_tsig, NameSpace.empty_table);

val PureN = "Pure";
val CPureN = "CPure";



(** signature content **)

(* naming *)

fun naming_of (Sg (_, {naming, ...})) = naming;

val base_name = NameSpace.base;
val full_name = NameSpace.full o naming_of;
fun full_name_path sg elems = NameSpace.full (NameSpace.add_path elems (naming_of sg));
val declare_name = NameSpace.declare o naming_of;


(* syntax *)

fun map_syntax f (Syn (syntax, trfuns)) = Syn (f syntax, trfuns);

fun make_syntax sg (Syn (syntax, (atrs, trs, tr's, atr's))) =
  let
    fun apply (c, (f, s)) = (c, (f sg, s));
    fun prep tab = map apply (Symtab.dest tab);
    fun prep' tab = map apply (Symtab.dest_multi tab);
  in syntax |> Syntax.extend_trfuns (prep atrs, prep trs, prep' tr's, prep' atr's) end;

fun syn_of (sg as Sg ({syn, ...}, _)) = make_syntax sg syn;


(* advanced translation functions *)

fun extend_trfuns (atrs, trs, tr's, atr's)
    (Syn (syn, (parse_ast_trtab, parse_trtab, print_trtab, print_ast_trtab))) =
  Syn (syn, (Syntax.extend_trtab "parse ast translation" atrs parse_ast_trtab,
    Syntax.extend_trtab "parse translation" trs parse_trtab,
    Syntax.extend_tr'tab tr's print_trtab,
    Syntax.extend_tr'tab atr's print_ast_trtab));

fun merge_trfuns
    (parse_ast_trtab1, parse_trtab1, print_trtab1, print_ast_trtab1)
    (parse_ast_trtab2, parse_trtab2, print_trtab2, print_ast_trtab2) =
  (Syntax.merge_trtabs "parse ast translation" parse_ast_trtab1 parse_ast_trtab2,
    Syntax.merge_trtabs "parse translation" parse_trtab1 parse_trtab2,
    Syntax.merge_tr'tabs print_trtab1 print_trtab2,
    Syntax.merge_tr'tabs print_ast_trtab1 print_ast_trtab2);


(* type signature *)

val tsig_of = #tsig o rep_sg;

val classes = Type.classes o tsig_of;
val defaultS = Type.defaultS o tsig_of;
val subsort = Type.subsort o tsig_of;
val of_sort = Type.of_sort o tsig_of;
val witness_sorts = Type.witness_sorts o tsig_of;
val universal_witness = Type.universal_witness o tsig_of;
val typ_instance = Type.typ_instance o tsig_of;
fun is_logtype sg c = c mem_string Type.logical_types (tsig_of sg);


(* consts signature *)

fun const_type (Sg (_, {consts, ...})) c = Option.map #1 (Symtab.lookup (#2 consts, c));

fun the_const_type sg c =
  (case const_type sg c of SOME T => T
  | NONE => raise TYPE ("Undeclared constant " ^ quote c, [], []));

fun declared_tyname sg c =
  is_some (Symtab.lookup (#2 (#types (Type.rep_tsig (tsig_of sg))), c));

fun declared_const sg c = is_some (const_type sg c);



(** intern / extern names **)

val class_space = #1 o #classes o Type.rep_tsig o tsig_of;
val type_space = #1 o #types o Type.rep_tsig o tsig_of;
val const_space = #1 o #consts o rep_sg

val intern_class = NameSpace.intern o class_space;
val extern_class = NameSpace.extern o class_space;
val intern_type = NameSpace.intern o type_space;
val extern_type = NameSpace.extern o type_space;
val intern_const = NameSpace.intern o const_space;
val extern_const = NameSpace.extern o const_space;

val intern_sort = map o intern_class;
val extern_sort = map o extern_class;

local

fun mapping add_names f t =
  let
    fun f' x = let val y = f x in if x = y then NONE else SOME (x, y) end;
    val tab = List.mapPartial f' (add_names (t, []));
    fun get x = if_none (assoc_string (tab, x)) x;
  in get end;

fun typ_mapping f g sg T =
  T |> Term.map_typ
    (mapping add_typ_classes (f sg) T)
    (mapping add_typ_tycons (g sg) T);

fun term_mapping f g h sg t =
  t |> Term.map_term
    (mapping add_term_classes (f sg) t)
    (mapping add_term_tycons (g sg) t)
    (mapping add_term_consts (h sg) t);

in

val intern_typ = typ_mapping intern_class intern_type;
val extern_typ = typ_mapping extern_class extern_type;
val intern_term = term_mapping intern_class intern_type intern_const;
val extern_term = term_mapping extern_class extern_type extern_const;
val intern_tycons = typ_mapping (K I) intern_type;

end;



(** pretty printing of terms, types etc. **)

fun pretty_term' syn sg t = Syntax.pretty_term syn (exists_stamp CPureN sg) (extern_term sg t);
fun pretty_term sg t = pretty_term' (syn_of sg) sg t;
fun pretty_typ sg T = Syntax.pretty_typ (syn_of sg) (extern_typ sg T);
fun pretty_sort sg S = Syntax.pretty_sort (syn_of sg) (extern_sort sg S);

fun pretty_classrel sg cs = Pretty.block (List.concat
  (separate [Pretty.str " <", Pretty.brk 1] (map (single o pretty_sort sg o single) cs)));

fun pretty_arity sg (a, Ss, S) =
  let
    val a' = extern_type sg a;
    val dom =
      if null Ss then []
      else [Pretty.list "(" ")" (map (pretty_sort sg) Ss), Pretty.brk 1];
  in Pretty.block ([Pretty.str (a' ^ " ::"), Pretty.brk 1] @ dom @ [pretty_sort sg S]) end;

val string_of_term = Pretty.string_of oo pretty_term;
val string_of_typ = Pretty.string_of oo pretty_typ;
val string_of_sort = Pretty.string_of oo pretty_sort;
val string_of_classrel = Pretty.string_of oo pretty_classrel;
val string_of_arity = Pretty.string_of oo pretty_arity;

val pprint_term = (Pretty.pprint o Pretty.quote) oo pretty_term;
val pprint_typ = (Pretty.pprint o Pretty.quote) oo pretty_typ;

fun pp sg = Pretty.pp (pretty_term sg, pretty_typ sg, pretty_sort sg,
  pretty_classrel sg, pretty_arity sg);



(** certify entities **)    (*exception TYPE*)

(* certify wrt. type signature *)

fun certify cert = cert o tsig_of o check_stale "Sign.certify";

val certify_class      = certify Type.cert_class;
val certify_sort       = certify Type.cert_sort;
val certify_typ        = certify Type.cert_typ;
val certify_typ_syntax = certify Type.cert_typ_syntax;
val certify_typ_abbrev = certify Type.cert_typ_abbrev;


(* certify_term *)

local

(*determine and check the type of a term*)
fun type_check pp tm =
  let
    fun err_appl why bs t T u U =
      let
        val xs = map Free bs;           (*we do not rename here*)
        val t' = subst_bounds (xs, t);
        val u' = subst_bounds (xs, u);
        val msg = cat_lines
          (TypeInfer.appl_error (Syntax.pp_show_brackets pp) why t' T u' U);
      in raise TYPE (msg, [T, U], [t', u']) end;

    fun typ_of (_, Const (_, T)) = T
      | typ_of (_, Free  (_, T)) = T
      | typ_of (_, Var (_, T)) = T
      | typ_of (bs, Bound i) = snd (List.nth (bs, i) handle Subscript =>
          raise TYPE ("Loose bound variable: B." ^ string_of_int i, [], [Bound i]))
      | typ_of (bs, Abs (x, T, body)) = T --> typ_of ((x, T) :: bs, body)
      | typ_of (bs, t $ u) =
          let val T = typ_of (bs, t) and U = typ_of (bs, u) in
            (case T of
              Type ("fun", [T1, T2]) =>
                if T1 = U then T2 else err_appl "Incompatible operand type" bs t T u U
            | _ => err_appl "Operator not of function type" bs t T u U)
          end;

  in typ_of ([], tm) end;

in

fun certify_term pp sg tm =
  let
    val _ = check_stale "Sign.certify_term" sg;

    val tm' = map_term_types (Type.cert_typ (tsig_of sg)) tm;
    val tm' = if tm = tm' then tm else tm';  (*avoid copying of already normal term*)

    fun err msg = raise TYPE (msg, [], [tm']);

    fun show_const a T = quote a ^ " :: " ^ Pretty.string_of_typ pp T;

    fun check_atoms (t $ u) = (check_atoms t; check_atoms u)
      | check_atoms (Abs (_, _, t)) = check_atoms t
      | check_atoms (Const (a, T)) =
          (case const_type sg a of
            NONE => err ("Undeclared constant " ^ show_const a T)
          | SOME U =>
              if typ_instance sg (T, U) then ()
              else err ("Illegal type for constant " ^ show_const a T))
      | check_atoms (Var ((x, i), _)) =
          if i < 0 then err ("Malformed variable: " ^ quote x) else ()
      | check_atoms _ = ();
  in
    check_atoms tm';
    (tm', type_check pp tm', maxidx_of_term tm')
  end;

end;



(** read and certify entities **)    (*exception ERROR/TYPE*)

(* sorts *)

fun read_sort' syn sg str =
  let
    val _ = check_stale "Sign.read_sort'" sg;
    val S = intern_sort sg (Syntax.read_sort syn str);
  in Type.cert_sort (tsig_of sg) S handle TYPE (msg, _, _) => error msg end;

fun read_sort sg str = read_sort' (syn_of sg) sg str;


(* types *)

local

fun gen_read_typ' cert syn (sg, def_sort) str =
  let
    val _ = check_stale "Sign.gen_read_typ'" sg;
    val get_sort = TypeInfer.get_sort (tsig_of sg) def_sort (intern_sort sg);
    val T = intern_tycons sg (Syntax.read_typ syn get_sort (intern_sort sg) str);
  in cert (tsig_of sg) T handle TYPE (msg, _, _) => error msg end
  handle ERROR => error ("The error(s) above occurred in type " ^ quote str);

fun gen_read_typ cert (sg, def_sort) str = gen_read_typ' cert (syn_of sg) (sg, def_sort) str;

in

fun no_def_sort sg = (sg, K NONE);

val read_typ'        = gen_read_typ' Type.cert_typ;
val read_typ_syntax' = gen_read_typ' Type.cert_typ_syntax;
val read_typ_abbrev' = gen_read_typ' Type.cert_typ_abbrev;
val read_typ         = gen_read_typ Type.cert_typ;
val read_typ_syntax  = gen_read_typ Type.cert_typ_syntax;
val read_typ_abbrev  = gen_read_typ Type.cert_typ_abbrev;

end;


(* type and constant names *)

fun read_tyname sg raw_c =
  let val c = intern_type sg raw_c in
    (case Symtab.lookup (#2 (#types (Type.rep_tsig (tsig_of sg))), c) of
      SOME (Type.LogicalType n, _) => Type (c, replicate n dummyT)
    | _ => error ("Undeclared type constructor: " ^ quote c))
  end;

fun read_const sg raw_c =
  let
    val c = intern_const sg raw_c;
    val _ = the_const_type sg c handle TYPE (msg, _, _) => error msg;
  in Const (c, dummyT) end;



(** infer_types **)         (*exception ERROR*)

(*
  def_type: partial map from indexnames to types (constrains Frees and Vars)
  def_sort: partial map from indexnames to sorts (constrains TFrees and TVars)
  used: list of already used type variables
  freeze: if true then generated parameters are turned into TFrees, else TVars

  termss: lists of alternative parses (only one combination should be type-correct)
  typs: expected types
*)

fun infer_types_simult pp sg def_type def_sort used freeze args =
  let
    val tsig = tsig_of sg;

    val termss = foldr multiply [[]] (map fst args);
    val typs =
      map (fn (_, T) => certify_typ sg T handle TYPE (msg, _, _) => error msg) args;

    fun infer ts = OK (TypeInfer.infer_types (Syntax.pp_show_brackets pp) tsig
        (const_type sg) def_type def_sort (intern_const sg) (intern_tycons sg)
        (intern_sort sg) used freeze typs ts)
      handle TYPE (msg, _, _) => Error msg;

    val err_results = map infer termss;
    val errs = List.mapPartial get_error err_results;
    val results = List.mapPartial get_ok err_results;

    val ambiguity = length termss;

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
      cat_lines (map (Pretty.string_of_term pp) (List.concat (map fst results)))))
  end;


fun infer_types pp sg def_type def_sort used freeze tsT =
  apfst hd (infer_types_simult pp sg def_type def_sort used freeze [tsT]);



(** read_def_terms -- read terms and infer types **)

fun read_def_terms' pp is_logtype syn (sg, types, sorts) used freeze sTs =
  let
    fun read (s, T) =
      let val T' = certify_typ sg T handle TYPE (msg, _, _) => error msg
      in (Syntax.read is_logtype syn T' s, T') end;
  in infer_types_simult pp sg types sorts used freeze (map read sTs) end;

fun read_def_terms (sg, types, sorts) =
  read_def_terms' (pp sg) (is_logtype sg) (syn_of sg) (sg, types, sorts);

fun simple_read_term sg T s =
  let val ([t], _) = read_def_terms (sg, K NONE, K NONE) [] true [(s, T)]
  in t end
  handle ERROR => error ("The error(s) above occurred for term " ^ s);



(** signature extension functions **)  (*exception ERROR/TYPE*)

(* add default sort *)

fun gen_add_defsort prep_sort s sg =
  sg |> map_tsig (Type.set_defsort (prep_sort sg s));

val add_defsort = gen_add_defsort read_sort;
val add_defsort_i = gen_add_defsort certify_sort;


(* add type constructors *)

fun add_types types sg = sg |> map_sign (fn (syn, tsig, consts) =>
  let
    val syn' = map_syntax (Syntax.extend_type_gram types) syn;
    val decls = map (fn (a, n, mx) => (Syntax.type_name a mx, n)) types;
    val tsig' = Type.add_types (naming_of sg) decls tsig;
  in (syn', tsig', consts) end);


(* add nonterminals *)

fun add_nonterminals bnames sg = sg |> map_sign (fn (syn, tsig, consts) =>
  let
    val syn' = map_syntax (Syntax.extend_consts bnames) syn;
    val tsig' = Type.add_nonterminals (naming_of sg) bnames tsig;
  in (syn', tsig', consts) end);


(* add type abbreviations *)

fun gen_add_tyabbr prep_typ (a, vs, rhs, mx) sg =
  sg |> map_sign (fn (syn, tsig, consts) =>
    let
      val syn' = map_syntax (Syntax.extend_type_gram [(a, length vs, mx)]) syn;
      val a' = Syntax.type_name a mx;
      val abbr = (a', vs, prep_typ sg rhs) handle ERROR =>
        error ("in type abbreviation " ^ quote a');
      val tsig' = Type.add_abbrevs (naming_of sg) [abbr] tsig;
    in (syn', tsig', consts) end);

val add_tyabbrs = fold (gen_add_tyabbr (read_typ_syntax o no_def_sort));
val add_tyabbrs_i = fold (gen_add_tyabbr certify_typ_syntax);


(* add type arities *)

fun gen_add_arities int_type prep_sort arities sg = sg |> map_tsig (fn tsig =>
  let
    fun prep_arity (a, Ss, S) = (int_type sg a, map (prep_sort sg) Ss, prep_sort sg S)
      handle ERROR => error ("in arity for type " ^ quote a);
    val tsig' = Type.add_arities (pp sg) (map prep_arity arities) tsig;
  in tsig' end);

val add_arities = gen_add_arities intern_type read_sort;
val add_arities_i = gen_add_arities (K I) certify_sort;


(* modify syntax *)

fun gen_syntax change_gram prep_typ (prmode, args) sg =
  let
    fun prep (c, T, mx) = (c, prep_typ sg T, mx) handle ERROR =>
      error ("in syntax declaration " ^ quote (Syntax.const_name c mx));
  in sg |> map_syn (map_syntax (change_gram (is_logtype sg) prmode (map prep args))) end;

fun gen_add_syntax x = gen_syntax Syntax.extend_const_gram x;

val add_modesyntax = gen_add_syntax (read_typ_syntax o no_def_sort);
val add_modesyntax_i = gen_add_syntax certify_typ_syntax;
val add_syntax = curry add_modesyntax Syntax.default_mode;
val add_syntax_i = curry add_modesyntax_i Syntax.default_mode;
val del_modesyntax = gen_syntax Syntax.remove_const_gram (read_typ_syntax o no_def_sort);
val del_modesyntax_i = gen_syntax Syntax.remove_const_gram certify_typ_syntax;


(* add constants *)

fun err_dup_consts cs =
  error ("Duplicate declaration of constant(s) " ^ commas_quote cs);

fun gen_add_consts prep_typ raw_args sg =
  let
    val prepT = compress_type o Type.varifyT o Type.no_tvars o Term.no_dummyT o prep_typ sg;
    fun prep (c, T, mx) = ((c, prepT T, mx) handle TYPE (msg, _, _) => error msg)
      handle ERROR => error ("in declaration of constant " ^ quote (Syntax.const_name c mx));
    val args = map prep raw_args;
    val decls = args |> map (fn (c, T, mx) => (Syntax.const_name c mx, (T, stamp ())));
    fun extend_consts consts = NameSpace.extend_table (naming_of sg) (consts, decls)
      handle Symtab.DUPS cs => err_dup_consts cs;
  in sg |> map_consts extend_consts |> add_syntax_i args end;

val add_consts = gen_add_consts (read_typ o no_def_sort);
val add_consts_i = gen_add_consts certify_typ;


(* add type classes *)

val classN = "_class";

val const_of_class = suffix classN;
fun class_of_const c = unsuffix classN c
  handle Fail _ => raise TERM ("class_of_const: bad name " ^ quote c, []);

fun gen_add_class int_class (bclass, raw_classes) sg =
  sg |> map_sign (fn (syn, tsig, consts) =>
    let
      val classes = map (int_class sg) raw_classes;
      val syn' = map_syntax (Syntax.extend_consts [bclass]) syn;
      val tsig' = Type.add_classes (pp sg) (naming_of sg) [(bclass, classes)] tsig;
    in (syn', tsig', consts) end)
  |> add_consts_i [(const_of_class bclass, a_itselfT --> propT, Syntax.NoSyn)];

val add_classes = fold (gen_add_class intern_class);
val add_classes_i = fold (gen_add_class (K I));


(* add to classrel *)

fun gen_add_classrel int_class raw_pairs sg = sg |> map_tsig (fn tsig =>
  let
    val pairs = map (pairself (int_class sg)) raw_pairs;
    val tsig' = Type.add_classrel (pp sg) pairs tsig;
  in tsig' end);

val add_classrel = gen_add_classrel intern_class;
val add_classrel_i = gen_add_classrel (K I);


(* add translation functions *)

local

fun mk trs = map Syntax.mk_trfun trs;

fun gen_add_trfuns ext non_typed (atrs, trs, tr's, atr's) sg = sg |> map_syn (fn syn =>
  let val syn' = syn |> ext (mk atrs, mk trs, mk (map (apsnd non_typed) tr's), mk atr's)
  in make_syntax sg syn'; syn' end);

fun gen_add_trfunsT ext tr's sg = sg |> map_syn (fn syn =>
  let val syn' = syn |> ext ([], [], mk tr's, [])
  in make_syntax sg syn'; syn' end);

in

val add_trfuns = gen_add_trfuns (map_syntax o Syntax.extend_trfuns) Syntax.non_typed_tr';
val add_trfunsT = gen_add_trfunsT (map_syntax o Syntax.extend_trfuns);
val add_advanced_trfuns = gen_add_trfuns extend_trfuns Syntax.non_typed_tr'';
val add_advanced_trfunsT = gen_add_trfunsT extend_trfuns;

end;

val add_tokentrfuns = map_syn o map_syntax o Syntax.extend_tokentrfuns;


(* add translation rules *)

fun add_trrules args sg = sg |> map_syn (fn syn =>
  let val rules = map (Syntax.map_trrule (apfst (intern_type sg))) args
  in map_syntax (Syntax.extend_trrules (is_logtype sg) (make_syntax sg syn) rules) syn end);

val add_trrules_i = map_syn o map_syntax o Syntax.extend_trrules_i;


(* modify naming *)

val add_path        = map_naming o NameSpace.add_path;
val qualified_names = map_naming NameSpace.qualified_names;
val no_base_names   = map_naming NameSpace.no_base_names;
val custom_accesses = map_naming o NameSpace.custom_accesses;
val set_policy      = map_naming o NameSpace.set_policy;
val restore_naming  = map_naming o K o naming_of;


(* hide names *)

fun hide_classes b xs sg = sg |> map_tsig (Type.hide_classes b (map (intern_class sg) xs));
val hide_classes_i = map_tsig oo Type.hide_classes;
fun hide_types b xs sg = sg |> map_tsig (Type.hide_types b (map (intern_type sg) xs));
val hide_types_i = map_tsig oo Type.hide_types;
fun hide_consts b xs sg =
  sg |> map_consts (apfst (fold (NameSpace.hide b o intern_const sg) xs));
val hide_consts_i = (map_consts o apfst) oo (fold o NameSpace.hide);



(** merge signatures **)

fun merge_stamps stamps1 stamps2 =
  let val stamps = merge_lists' stamps1 stamps2 in
    (case duplicates (map ! stamps) of
      [] => stamps
    | dups => error ("Attempt to merge different versions of theories " ^ commas_quote dups))
  end;


(* trivial merge *)

fun merge_refs (sgr1 as SgRef (SOME (ref (sg1 as Sg ({stamps = s1, ...}, _)))),
        sgr2 as SgRef (SOME (ref (sg2 as Sg ({stamps = s2, ...}, _))))) =
      if subsig (sg2, sg1) then sgr1
      else if subsig (sg1, sg2) then sgr2
      else (merge_stamps s1 s2;  (*check for different versions*)
        error ("Attempt to do non-trivial merge of signature\n" ^
          str_of_sg sg1 ^ " and " ^ str_of_sg sg2))
  | merge_refs _ = sys_error "Sign.merge_refs";

val merge = deref o merge_refs o pairself self_ref;


(* non-trivial merge *)              (*exception TERM/ERROR*)

local

fun nontriv_merge (sg1, sg2) =
  if subsig_internal (sg2, sg1) then sg1
  else if subsig_internal (sg1, sg2) then sg2
  else
    if exists_stamp CPureN sg1 <> exists_stamp CPureN sg2
    then error "Cannot merge Pure and CPure developments"
  else
    let
      val Sg ({id = _, stamps = stamps1, syn = Syn (syntax1, trfuns1)},
          {self = _, tsig = tsig1, consts = consts1, naming = _, data = data1}) = sg1;
      val Sg ({id = _, stamps = stamps2, syn = Syn (syntax2, trfuns2)},
          {self = _, tsig = tsig2, consts = consts2, naming = _, data = data2}) = sg2;

      val stamps = merge_stamps stamps1 stamps2;
      val syntax = Syntax.merge_syntaxes syntax1 syntax2;
      val trfuns = merge_trfuns trfuns1 trfuns2;
      val syn = Syn (syntax, trfuns);
      val consts = NameSpace.merge_tables eq_snd (consts1, consts2)
        handle Symtab.DUPS cs => err_dup_consts cs;
      val naming = NameSpace.default_naming;
      val data = merge_data (data1, data2);

      val pre_sg = make_sg (ref "", SgRef (SOME (ref dummy_sg)), ref "#" :: stamps1)
        naming data (syn, tsig1, consts);
      val tsig = Type.merge_tsigs (pp pre_sg) (tsig1, tsig2);

      val self = SgRef (SOME (ref dummy_sg));
      val sg = make_sg (ref "", self, stamps) naming data (syn, tsig, consts);
    in assign self sg; syn_of sg; sg end;

in

fun prep_ext_merge sgs =
  if null sgs then
    error "Merge: no parent theories"
  else if exists is_draft sgs then
    error "Attempt to merge draft theories"
  else
    Library.foldl nontriv_merge (hd sgs, tl sgs)
    |> prep_ext
    |> add_path "/";

end;

end;
