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
    tsig: Type.tsig,
    consts: (typ * stamp) Symtab.table,
    path: string list option,
    spaces: (string * NameSpace.T) list,
    data: data}
  val name_of: sg -> string
  val stamp_names_of: sg -> string list
  val exists_stamp: string -> sg -> bool
  val tsig_of: sg -> Type.tsig
  val is_logtype: sg -> string -> bool
  val deref: sg_ref -> sg
  val self_ref: sg -> sg_ref
  val subsig: sg * sg -> bool
  val joinable: sg * sg -> bool
  val eq_sg: sg * sg -> bool
  val same_sg: sg * sg -> bool
  val is_draft: sg -> bool
  val is_stale: sg -> bool
  val syn_of: sg -> Syntax.syntax
  val const_type: sg -> string -> typ option
  val classes: sg -> class list
  val defaultS: sg -> sort
  val subsort: sg -> sort * sort -> bool
  val nodup_vars: term -> term
  val of_sort: sg -> typ * sort -> bool
  val witness_sorts: sg -> sort list -> sort list -> (typ * sort) list
  val universal_witness: sg -> (typ * sort) option
  val typ_instance: sg -> typ * typ -> bool
  val classK: string
  val typeK: string
  val constK: string
  val full_name: sg -> bstring -> string
  val full_name_path: sg -> string -> bstring -> string
  val base_name: string -> bstring
  val intern: sg -> string -> xstring -> string
  val extern: sg -> string -> string -> xstring
  val cond_extern: sg -> string -> string -> xstring
  val cond_extern_table: sg -> string -> 'a Symtab.table -> (xstring * 'a) list
  val extern_typ: sg -> typ -> typ
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
  val PureN: string
  val CPureN: string
  val pre_pure: sg
  val pretty_term: sg -> term -> Pretty.T
  val pretty_term': Syntax.syntax -> sg -> term -> Pretty.T
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
  val certify_typ_raw: sg -> typ -> typ
  val certify_tyname: sg -> string -> string
  val certify_const: sg -> string -> string
  val certify_term: Pretty.pp -> sg -> term -> term * typ * int
  val read_sort: sg -> string -> sort
  val read_raw_typ: sg * (indexname -> sort option) -> string -> typ
  val read_typ: sg * (indexname -> sort option) -> string -> typ
  val read_typ': Syntax.syntax -> sg * (indexname -> sort option) -> string -> typ
  val read_typ_raw': Syntax.syntax -> sg * (indexname -> sort option) -> string -> typ
  val inst_typ_tvars: sg -> (indexname * typ) list -> typ -> typ
  val inst_term_tvars: sg -> (indexname * typ) list -> term -> term
  val infer_types: Pretty.pp -> sg -> (indexname -> typ option) ->
    (indexname -> sort option) -> string list -> bool
    -> xterm list * typ -> term * (indexname * typ) list
  val infer_types_simult: Pretty.pp -> sg -> (indexname -> typ option) ->
    (indexname -> sort option) -> string list -> bool
    -> (xterm list * typ) list -> term list * (indexname * typ) list
  val read_def_terms': Pretty.pp -> (string -> bool) -> Syntax.syntax ->
    sg * (indexname -> typ option) * (indexname -> sort option) ->
    string list -> bool -> (string * typ) list -> term list * (indexname * typ) list
  val read_def_terms:
    sg * (indexname -> typ option) * (indexname -> sort option) ->
    string list -> bool -> (string * typ) list -> term list * (indexname * typ) list
  val simple_read_term: sg -> typ -> string -> term
  val const_of_class: class -> string
  val class_of_const: string -> class
  val add_classes: (bclass * xclass list) list -> sg -> sg
  val add_classes_i: (bclass * class list) list -> sg -> sg
  val add_classrel: (xclass * xclass) list -> sg -> sg
  val add_classrel_i: (class * class) list -> sg -> sg
  val add_defsort: string -> sg -> sg
  val add_defsort_i: sort -> sg -> sg
  val add_types: (bstring * int * mixfix) list -> sg -> sg
  val add_nonterminals: bstring list -> sg -> sg
  val add_tyabbrs: (bstring * string list * string * mixfix) list -> sg -> sg
  val add_tyabbrs_i: (bstring * string list * typ * mixfix) list -> sg -> sg
  val add_arities: (xstring * string list * string) list -> sg -> sg
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
  val add_space: string * string list -> sg -> sg
  val hide_space: bool -> string * string list -> sg -> sg
  val hide_space_i: bool -> string * string list -> sg -> sg
  val add_name: string -> sg -> sg
  val data_kinds: data -> string list
  val merge_refs: sg_ref * sg_ref -> sg_ref
  val merge: sg * sg -> sg
  val copy: sg -> sg
  val prep_ext: sg -> sg
  val nontriv_merge: sg * sg -> sg
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
   {id: string ref,                             (*id*)
    stamps: string ref list,                    (*unique theory indentifier*)
    syn: syn} *                                 (*syntax for parsing and printing*)
   {self: sg_ref,                               (*mutable self reference*)
    tsig: Type.tsig,                            (*order-sorted signature of types*)
    consts: (typ * stamp) Symtab.table,         (*type schemes of constants*)
    path: string list option,                   (*current name space entry prefix*)
    spaces: (string * NameSpace.T) list,        (*name spaces for consts, types etc.*)
    data: data}                                 (*anytype data*)
and data =
  Data of
    (Object.kind *                              (*kind (for authorization)*)
      (Object.T *                               (*value*)
        ((Object.T -> Object.T) *               (*copy method*)
          (Object.T -> Object.T) *              (*prepare extend method*)
          (Object.T * Object.T -> Object.T) *   (*merge and prepare extend method*)
          (sg -> Object.T -> unit))))           (*print method*)
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

(*make signature*)
fun make_sign (id, self, tsig, consts, syn, path, spaces, data, stamps) =
  Sg ({id = id, stamps = stamps, syn = syn}, {self = self, tsig = tsig,
    consts = consts, path = path, spaces = spaces, data = data});


(* basic operations *)

fun rep_sg (Sg (_, args)) = args;

fun stamp_names_of (Sg ({stamps, ...}, _)) = rev (map ! stamps);
fun exists_stamp name (Sg ({stamps, ...}, _)) = exists (equal name o !) stamps;
fun pretty_sg sg = Pretty.str_list "{" "}" (stamp_names_of sg);
val str_of_sg = Pretty.str_of o pretty_sg;
val pprint_sg = Pretty.pprint o pretty_sg;

val tsig_of = #tsig o rep_sg;
fun is_logtype sg c = c mem_string Type.logical_types (tsig_of sg);
fun const_type (Sg (_, {consts, ...})) c = apsome #1 (Symtab.lookup (consts, c));


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


fun joinable (sg1, sg2) = subsig (sg1, sg2) orelse subsig (sg2, sg1);

(*test if same theory names are contained in signatures' stamps,
  i.e. if signatures belong to same theory but not necessarily to the
  same version of it*)
fun same_sg (sg1 as Sg ({stamps = s1, ...}, _), sg2 as Sg ({stamps = s2, ...}, _)) =
  eq_sg (sg1, sg2) orelse eq_set_string (pairself (map (op !)) (s1, s2));

(*test for drafts*)
fun is_draft (Sg ({stamps = ref name :: _, ...}, _)) =
  name = "" orelse ord name = ord "#";


(* syntax *)

fun map_syntax f (Syn (syntax, trfuns)) = Syn (f syntax, trfuns);

fun make_syntax sg (Syn (syntax, (atrs, trs, tr's, atr's))) =
  let
    fun apply (s, (f, _: stamp)) = (s, f sg);
    fun prep tab = map apply (Symtab.dest tab);
    fun prep' tab = map apply (Symtab.dest_multi tab);
  in syntax |> Syntax.extend_trfuns (prep atrs, prep trs, prep' tr's, prep' atr's) end;

fun syn_of (sg as Sg ({syn, ...}, _)) = make_syntax sg syn;


(* advanced translation functions *)

fun extend_trfuns (atrs, trs, tr's, atr's)
    (Syn (syn, (parse_ast_trtab, parse_trtab, print_trtab, print_ast_trtab))) =
  Syn (syn, (Syntax.extend_trtab parse_ast_trtab atrs "parse ast translation",
    Syntax.extend_trtab parse_trtab trs "parse translation",
    Syntax.extend_tr'tab print_trtab tr's,
    Syntax.extend_tr'tab print_ast_trtab atr's));

fun merge_trfuns
    (parse_ast_trtab1, parse_trtab1, print_trtab1, print_ast_trtab1)
    (parse_ast_trtab2, parse_trtab2, print_trtab2, print_ast_trtab2) =
  (Syntax.merge_trtabs parse_ast_trtab1 parse_ast_trtab2 "parse ast translation",
    Syntax.merge_trtabs parse_trtab1 parse_trtab2 "parse translation",
    Syntax.merge_tr'tabs print_trtab1 print_trtab2,
    Syntax.merge_tr'tabs print_ast_trtab1 print_ast_trtab2);


(* classes and sorts *)

val classes = Type.classes o tsig_of;
val defaultS = Type.defaultS o tsig_of;
val subsort = Type.subsort o tsig_of;
val of_sort = Type.of_sort o tsig_of;
val witness_sorts = Type.witness_sorts o tsig_of;
val universal_witness = Type.universal_witness o tsig_of;
val typ_instance = Type.typ_instance o tsig_of;



(** signature data **)

(* errors *)

fun of_theory sg = "\nof theory " ^ str_of_sg sg;

fun err_inconsistent kinds =
  error ("Attempt to merge different versions of " ^ commas_quote kinds ^ " data");

fun err_method name kind e =
  (writeln ("Error while invoking " ^ quote kind ^ " " ^ name ^ " method"); raise e);

fun err_dup_init sg kind =
  error ("Duplicate initialization of " ^ quote kind ^ " data" ^ of_theory sg);

fun err_uninit sg kind =
  error ("Tried to access uninitialized " ^ quote kind ^ " data" ^ of_theory sg);

(*Trying to access theory data using get / put operations from a different
  instance of the TheoryDataFun result.  Typical cure: re-load all files*)
fun err_access sg kind =
  error ("Unauthorized access to " ^ quote kind ^ " data" ^ of_theory sg);


(* prepare data *)

val empty_data = Data Symtab.empty;

fun merge_data (Data tab1, Data tab2) =
  let
    val data1 = map snd (Symtab.dest tab1);
    val data2 = map snd (Symtab.dest tab2);
    val all_data = data1 @ data2;
    val kinds = gen_distinct Object.eq_kind (map fst all_data);

   fun entry data kind =
     (case gen_assoc Object.eq_kind (data, kind) of
       None => []
     | Some x => [(kind, x)]);

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

fun init_data_sg sg (Data tab) kind e cp ext mrg prt =
  let val name = Object.name_of_kind kind in
    Data (Symtab.update_new ((name, (kind, (e, (cp, ext, mrg, prt)))), tab))
      handle Symtab.DUP _ => err_dup_init sg name
  end;


(* access data *)

fun data_kinds (Data tab) = map fst (Symtab.dest tab);

fun lookup_data sg tab kind =
  let val name = Object.name_of_kind kind in
    (case Symtab.lookup (tab, name) of
      Some (k, x) =>
        if Object.eq_kind (kind, k) then x
        else err_access sg name
    | None => err_uninit sg name)
  end;

fun get_data kind f (sg as Sg (_, {data = Data tab, ...})) =
  let val x = fst (lookup_data sg tab kind)
  in f x handle Match => Object.kind_error kind end;

fun print_data kind (sg as Sg (_, {data = Data tab, ...})) =
  let val (e, (_, _, _, prt)) = lookup_data sg tab kind
  in prt sg e handle exn => err_method ("print" ^ of_theory sg) (Object.name_of_kind kind) exn end;

fun put_data_sg sg (Data tab) kind f x =
  Data (Symtab.update ((Object.name_of_kind kind,
    (kind, (f x, snd (lookup_data sg tab kind)))), tab));



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
    (sg as Sg ({id = _, stamps, syn}, {self, tsig, consts, path, spaces, data})) =
  let
    val _ = check_stale sg;
    val (self', data') =
      if is_draft sg andalso keep then (self, data)
      else (SgRef (Some (ref sg)), prep_ext_data data);
  in
    create_sign self' stamps name
      (extfun sg (syn, tsig, consts, (path, spaces), data') decls)
  end;



(** name spaces **)

(* kinds *)

val classK = "class";
val typeK = "type";
val constK = "const";


(* declare and retrieve names *)

fun space_of spaces kind =
  if_none (assoc (spaces, kind)) NameSpace.empty;

(*input and output of qualified names*)
fun intrn spaces kind = NameSpace.intern (space_of spaces kind);
fun extrn spaces kind = NameSpace.extern (space_of spaces kind);
fun cond_extrn spaces kind = NameSpace.cond_extern (space_of spaces kind);
fun cond_extrn_table spaces kind tab = NameSpace.cond_extern_table (space_of spaces kind) tab;

(*add / hide names*)
fun change_space f spaces kind x = overwrite (spaces, (kind, f (space_of spaces kind, x)));
fun add_names x = change_space NameSpace.extend x;
fun hide_names b x = change_space (NameSpace.hide b) x;

(*make full names*)
fun full _ "" = error "Attempt to declare empty name \"\""
  | full None bname = bname
  | full (Some path) bname =
      if NameSpace.is_qualified bname then
        error ("Attempt to declare qualified name " ^ quote bname)
      else
        let val name = NameSpace.pack (path @ [bname]) in
          if Syntax.is_identifier bname then ()
          else warning ("Declared non-identifier " ^ quote name); name
        end;

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
  fun extrn_class spaces = cond_extrn spaces classK;

  val intrn_sort = map o intrn_class;
  val intrn_typ = trn_typ o intrn;
  val intrn_term = trn_term o intrn;

  val extrn_sort = map o extrn_class;
  val extrn_typ = trn_typ o cond_extrn;
  val extrn_term = trn_term o cond_extrn;

  fun intrn_tycons spaces T =
    map_typ I (mapping (intrn spaces typeK) add_typ_tycons T) T;

  val intern = intrn o spaces_of;
  val extern = extrn o spaces_of;
  val cond_extern = cond_extrn o spaces_of;
  fun cond_extern_table sg = cond_extrn_table (spaces_of sg);

  fun extern_typ (sg as Sg (_, {spaces, ...})) T =
       if ! NameSpace.long_names then T else extrn_typ spaces T;

  val intern_class = intrn_class o spaces_of;
  val intern_sort = intrn_sort o spaces_of;
  val intern_typ = intrn_typ o spaces_of;
  val intern_term = intrn_term o spaces_of;

  fun intern_tycon sg = intrn (spaces_of sg) typeK;
  fun intern_const sg = intrn (spaces_of sg) constK;

  val intern_tycons = intrn_tycons o spaces_of;

  val full_name = full o #path o rep_sg;

  fun full_name_path sg elems =
    full (Some (if_none (#path (rep_sg sg)) [] @ NameSpace.unpack elems));

end;



(** partial Pure signature **)

val pure_syn =
  Syn (Syntax.pure_syn, (Symtab.empty, Symtab.empty, Symtab.empty, Symtab.empty));

val dummy_sg = make_sign (ref "", SgRef None, Type.empty_tsig,
  Symtab.empty, pure_syn, Some [], [], empty_data, []);

val pre_pure =
  create_sign (SgRef (Some (ref dummy_sg))) [] "#"
    (pure_syn, Type.empty_tsig, Symtab.empty, (Some [], []), empty_data);

val PureN = "Pure";
val CPureN = "CPure";



(** pretty printing of terms, types etc. **)

fun pretty_term' syn (sg as Sg ({stamps, ...}, {spaces, ...})) t =
  Syntax.pretty_term syn
    (exists (equal CPureN o !) stamps)
    (if ! NameSpace.long_names then t else extrn_term spaces t);

fun pretty_term sg t = pretty_term' (syn_of sg) sg t;

fun pretty_typ sg T =
  Syntax.pretty_typ (syn_of sg) (extern_typ sg T);

fun pretty_sort (sg as Sg (_, {spaces, ...})) S =
  Syntax.pretty_sort (syn_of sg)
    (if ! NameSpace.long_names then S else extrn_sort spaces S);

fun pretty_classrel sg cs = Pretty.block (flat
  (separate [Pretty.str " <", Pretty.brk 1] (map (single o pretty_sort sg o single) cs)));

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

val string_of_term = Pretty.string_of oo pretty_term;
val string_of_typ = Pretty.string_of oo pretty_typ;
val string_of_sort = Pretty.string_of oo pretty_sort;
val string_of_classrel = Pretty.string_of oo pretty_classrel;
val string_of_arity = Pretty.string_of oo pretty_arity;

fun pprint_term sg = Pretty.pprint o Pretty.quote o (pretty_term sg);
fun pprint_typ sg = Pretty.pprint o Pretty.quote o (pretty_typ sg);

fun pp sg = Pretty.pp (pretty_term sg, pretty_typ sg, pretty_sort sg,
  pretty_classrel sg, pretty_arity sg);



(** read sorts **)  (*exception ERROR*)

fun err_in_sort s =
  error ("The error(s) above occurred in sort " ^ quote s);

fun rd_sort sg syn tsig spaces str =
  let val S = intrn_sort spaces (Syntax.read_sort (make_syntax sg syn) str
    handle ERROR => err_in_sort str)
  in Type.cert_sort tsig S handle TYPE (msg, _, _) => (error_msg msg; err_in_sort str) end;

(*read and certify sort wrt a signature*)
fun read_sort (sg as Sg ({syn, ...}, {tsig, spaces, ...})) str =
  (check_stale sg; rd_sort sg syn tsig spaces str);

fun cert_sort _ _ tsig _ = Type.cert_sort tsig;



(** read types **)  (*exception ERROR*)

fun err_in_type s =
  error ("The error(s) above occurred in type " ^ quote s);

fun rd_raw_typ syn tsig spaces def_sort str =
  intrn_tycons spaces (Syntax.read_typ syn
    (TypeInfer.get_sort tsig def_sort (intrn_sort spaces)) (intrn_sort spaces) str
      handle ERROR => err_in_type str);

fun read_raw_typ' syn (sg as Sg (_, {tsig, spaces, ...}), def_sort) str =
  (check_stale sg; rd_raw_typ syn tsig spaces def_sort str);

fun read_raw_typ (sg, def_sort) = read_raw_typ' (syn_of sg) (sg, def_sort);

(*read and certify typ wrt a signature*)
local
  fun read_typ_aux rd cert (sg, def_sort) str =
    (#1 (cert (tsig_of sg) (rd (sg, def_sort) str))
      handle TYPE (msg, _, _) => (error_msg msg; err_in_type str));
in
  val read_typ          = read_typ_aux read_raw_typ Type.cert_typ;
  val read_typ_raw      = read_typ_aux read_raw_typ Type.cert_typ_raw;
  fun read_typ' syn     = read_typ_aux (read_raw_typ' syn) Type.cert_typ;
  fun read_typ_raw' syn = read_typ_aux (read_raw_typ' syn) Type.cert_typ_raw;
end;



(** certify classes, sorts, types and terms **)   (*exception TYPE*)

val certify_class = Type.cert_class o tsig_of;
val certify_sort = Type.cert_sort o tsig_of;
val certify_typ = #1 oo (Type.cert_typ o tsig_of);
val certify_typ_raw = #1 oo (Type.cert_typ_raw o tsig_of);

fun certify_tyname sg c =
  if is_some (Symtab.lookup (#types (Type.rep_tsig (tsig_of sg)), c)) then c
  else raise TYPE ("Undeclared type constructor: " ^ quote c, [], []);

fun certify_const sg c =
  if is_some (const_type sg c) then c
  else raise TYPE ("Undeclared constant: " ^ quote c, [], []);


(* certify_term *)

local

(*certify types of term and compute maxidx*)
fun cert_term_types certT =
  let
    fun cert (Const (a, T)) = let val (T', i) = certT T in (Const (a, T'), i) end
      | cert (Free (a, T)) = let val (T', i) = certT T in (Free (a, T'), i) end
      | cert (Var (xi as (_, i), T)) =
          let val (T', j) = certT T in (Var (xi, T'), Int.max (i, j)) end
      | cert (t as Bound _) = (t, ~1)
      | cert (Abs (a, T, t)) =
          let val (T', i) = certT T and (t', j) = cert t
          in (Abs (a, T', t'), Int.max (i, j)) end
      | cert (t $ u) =
          let val (t', i) = cert t and (u', j) =  cert u
          in (t' $ u', Int.max (i, j)) end;
  in cert end;

(*compute and check type of the term*)
fun type_check pp sg tm =
  let
    fun err_appl why bs t T u U =
      let
        val xs = map Free bs;           (*we do not rename here*)
        val t' = subst_bounds (xs, t);
        val u' = subst_bounds (xs, u);
        val text = cat_lines
          (TypeInfer.appl_error (Syntax.pp_show_brackets pp) why t' T u' U);
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
                if T1 = U then T2 else err_appl "Incompatible operand type" bs t T u U
            | _ => err_appl "Operator not of function type" bs t T u U)
          end;

  in typ_of ([], tm) end;

(*check for duplicate occurrences of TFree/TVar with distinct sorts*)
fun nodup_tvars (env, Type (_, Ts)) = nodup_tvars_list (env, Ts)
  | nodup_tvars (env as (tfrees, tvars), T as TFree (v as (a, S))) =
      (case assoc_string (tfrees, a) of
        Some S' =>
          if S = S' then env
          else raise TYPE ("Type variable " ^ quote a ^
            " has two distinct sorts", [TFree (a, S'), T], [])
      | None => (v :: tfrees, tvars))
  | nodup_tvars (env as (tfrees, tvars), T as TVar (v as (a, S))) =
      (case assoc_string_int (tvars, a) of
        Some S' =>
          if S = S' then env
          else raise TYPE ("Type variable " ^ quote (Syntax.string_of_vname a) ^
            " has two distinct sorts", [TVar (a, S'), T], [])
      | None => (tfrees, v :: tvars))
(*equivalent to foldl nodup_tvars_list, but 3X faster under Poly/ML*)
and nodup_tvars_list (env, []) = env
  | nodup_tvars_list (env, T :: Ts) = nodup_tvars_list (nodup_tvars (env, T), Ts);

in

(*check for duplicate occurrences of Free/Var with distinct types*)
fun nodup_vars tm =
  let
    fun nodups (envs as (env as (frees, vars), envT)) tm =
      (case tm of
        Const (c, T) => (env, nodup_tvars (envT, T))
      | Free (v as (a, T)) =>
          (case assoc_string (frees, a) of
            Some T' =>
              if T = T' then (env, nodup_tvars (envT, T))
              else raise TYPE ("Variable " ^ quote a ^
                " has two distinct types", [T', T], [])
          | None => ((v :: frees, vars), nodup_tvars (envT, T)))
      | Var (v as (ixn, T)) =>
          (case assoc_string_int (vars, ixn) of
            Some T' =>
              if T = T' then (env, nodup_tvars (envT, T))
              else raise TYPE ("Variable " ^ quote (Syntax.string_of_vname ixn) ^
                " has two distinct types", [T', T], [])
          | None => ((frees, v :: vars), nodup_tvars (envT, T)))
      | Bound _ => envs
      | Abs (_, T, t) => nodups (env, nodup_tvars (envT, T)) t
      | s $ t => nodups (nodups envs s) t)
  in nodups (([], []), ([], [])) tm; tm end;

fun certify_term pp sg tm =
  let
    val _ = check_stale sg;

    val (tm', maxidx) = cert_term_types (Type.cert_typ (tsig_of sg)) tm;
    val tm' = if tm = tm' then tm else tm';  (*avoid copying of already normal term*)

    fun err msg = raise TYPE (msg, [], [tm']);

    fun show_const a T = quote a ^ " :: " ^ Pretty.string_of_typ pp T;

    fun check_atoms (t $ u) = (check_atoms t; check_atoms u)
      | check_atoms (Abs (_, _, t)) = check_atoms t
      | check_atoms (Const (a, T)) =
          (case const_type sg a of
            None => err ("Undeclared constant " ^ show_const a T)
          | Some U =>
              if typ_instance sg (T, U) then ()
              else err ("Illegal type for constant " ^ show_const a T))
      | check_atoms (Var ((x, i), _)) =
          if i < 0 then err ("Malformed variable: " ^ quote x) else ()
      | check_atoms _ = ();
  in
    check_atoms tm';
    nodup_vars tm';
    (tm', type_check pp sg tm', maxidx)
  end;

end;



(** instantiation **)

fun inst_typ_tvars sg = Type.inst_typ_tvars (pp sg) (tsig_of sg);
fun inst_term_tvars sg = Type.inst_term_tvars (pp sg) (tsig_of sg);



(** infer_types **)         (*exception ERROR*)

(*
  def_type: partial map from indexnames to types (constrains Frees, Vars)
  def_sort: partial map from indexnames to sorts (constrains TFrees, TVars)
  used: list of already used type variables
  freeze: if true then generated parameters are turned into TFrees, else TVars

  termss: lists of alternative parses (only one combination should be type-correct)
  typs: expected types
*)

fun infer_types_simult pp sg def_type def_sort used freeze args =
  let
    val tsig = tsig_of sg;

    val termss = foldr multiply (map fst args, [[]]);
    val typs =
      map (fn (_, T) => certify_typ sg T handle TYPE (msg, _, _) => error msg) args;

    fun infer ts = OK (TypeInfer.infer_types (Syntax.pp_show_brackets pp) tsig
        (const_type sg) def_type def_sort (intern_const sg) (intern_tycons sg)
        (intern_sort sg) used freeze typs ts)
      handle TYPE (msg, _, _) => Error msg;

    val err_results = map infer termss;
    val errs = mapfilter get_error err_results;
    val results = mapfilter get_ok err_results;

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
      cat_lines (map (Pretty.string_of_term pp) (flat (map fst results)))))
  end;


fun infer_types pp sg def_type def_sort used freeze tsT =
  apfst hd (infer_types_simult pp sg def_type def_sort used freeze [tsT]);


(** read_def_terms **)

(*read terms, infer types*)
fun read_def_terms' pp is_logtype syn (sign, types, sorts) used freeze sTs =
  let
    fun read (s, T) =
      let val T' = certify_typ sign T handle TYPE (msg, _, _) => error msg
      in (Syntax.read is_logtype syn T' s, T') end;
    val tsTs = map read sTs;
  in infer_types_simult pp sign types sorts used freeze tsTs end;

fun read_def_terms (sign, types, sorts) =
  read_def_terms' (pp sign) (is_logtype sign) (syn_of sign) (sign, types, sorts);

fun simple_read_term sign T s =
  (read_def_terms (sign, K None, K None) [] true [(s, T)]
    handle ERROR => error ("The error(s) above occurred for " ^ s)) |> #1 |> hd;



(** extend signature **)    (*exception ERROR*)

(** signature extension functions **)  (*exception ERROR*)

fun decls_of path name_of mfixs =
  map (fn (x, y, mx) => (full path (name_of x mx), y)) mfixs;

fun no_read _ _ _ _ decl = decl;


(* add default sort *)

fun ext_defS prep_sort sg (syn, tsig, ctab, (path, spaces), data) S =
  (syn, Type.set_defsort (prep_sort sg syn tsig spaces S) tsig,
    ctab, (path, spaces), data);

fun ext_defsort arg = ext_defS rd_sort arg;
fun ext_defsort_i arg = ext_defS cert_sort arg;


(* add type constructors *)

fun ext_types sg (syn, tsig, ctab, (path, spaces), data) types =
  let
    val decls = decls_of path Syntax.type_name types;
    val syn' = map_syntax (Syntax.extend_type_gram types) syn;
    val tsig' = Type.add_types decls tsig;
  in (syn', tsig', ctab, (path, add_names spaces typeK (map fst decls)), data) end;


(* add type abbreviations *)

fun read_abbr sg syn tsig spaces (t, vs, rhs_src) =
  (t, vs, rd_raw_typ (make_syntax sg syn) tsig spaces (K None) rhs_src)
    handle ERROR => error ("in type abbreviation " ^ t);

fun ext_abbrs rd_abbr sg (syn, tsig, ctab, (path, spaces), data) abbrs =
  let
    fun mfix_of (t, vs, _, mx) = (t, length vs, mx);
    val syn' = syn |> map_syntax (Syntax.extend_type_gram (map mfix_of abbrs));

    val abbrs' =
      map (fn (t, vs, rhs, mx) =>
        (full path (Syntax.type_name t mx), vs, rhs)) abbrs;
    val spaces' = add_names spaces typeK (map #1 abbrs');
    val decls = map (rd_abbr sg syn' tsig spaces') abbrs';
  in (syn', Type.add_abbrs decls tsig, ctab, (path, spaces'), data) end;

fun ext_tyabbrs abbrs = ext_abbrs read_abbr abbrs;
fun ext_tyabbrs_i abbrs = ext_abbrs no_read abbrs;


(* add nonterminals *)

fun ext_nonterminals _ (syn, tsig, ctab, (path, spaces), data) bnames =
  let val names = map (full path) bnames in
    (map_syntax (Syntax.extend_consts names) syn,
      Type.add_nonterminals names tsig, ctab,
      (path, add_names spaces typeK names), data)
  end;


(* add type arities *)

fun ext_ars int prep_sort sg (syn, tsig, ctab, (path, spaces), data) arities =
  let
    val prepS = prep_sort sg syn tsig spaces;
    fun prep_arity (c, Ss, S) =
      (if int then intrn spaces typeK c else c, map prepS Ss, prepS S);
    val tsig' = Type.add_arities (pp sg) (map prep_arity arities) tsig;
  in (syn, tsig', ctab, (path, spaces), data) end;

fun ext_arities arg = ext_ars true rd_sort arg;
fun ext_arities_i arg = ext_ars false cert_sort arg;


(* add term constants and syntax *)

fun const_name path c mx =
  full path (Syntax.const_name c mx);

fun err_in_const c =
  error ("in declaration of constant " ^ quote c);

fun err_dup_consts cs =
  error ("Duplicate declaration of constant(s) " ^ commas_quote cs);


fun read_const sg syn tsig (path, spaces) (c, ty_src, mx) =
  (c, rd_raw_typ (make_syntax sg syn) tsig spaces (K None) ty_src, mx)
    handle ERROR => err_in_const (const_name path c mx);

fun ext_cnsts rd_const syn_only prmode sg (syn, tsig, ctab, (path, spaces), data)
    raw_consts =
  let
    val prep_typ = compress_type o Type.varifyT o Type.no_tvars o
     (if syn_only then #1 o Type.cert_typ_syntax tsig
      else Term.no_dummyT o #1 o Type.cert_typ tsig);
    fun prep_const (c, ty, mx) = (c, prep_typ ty, mx) handle TYPE (msg, _, _) =>
      (error_msg msg; err_in_const (const_name path c mx));

    val consts = map (prep_const o rd_const sg syn tsig (path, spaces)) raw_consts;
    val decls =
      if syn_only then []
      else decls_of path Syntax.const_name consts;
  in
    (map_syntax (Syntax.extend_const_gram (is_logtype sg) prmode consts) syn, tsig,
      Symtab.extend (ctab, map (fn (c, T) => (c, (T, stamp ()))) decls)
        handle Symtab.DUPS cs => err_dup_consts cs,
      (path, add_names spaces constK (map fst decls)), data)
  end;

fun ext_consts_i x = ext_cnsts no_read false Syntax.default_mode x;
fun ext_consts x = ext_cnsts read_const false Syntax.default_mode x;
fun ext_syntax_i x = ext_cnsts no_read true Syntax.default_mode x;
fun ext_syntax x = ext_cnsts read_const true Syntax.default_mode x;
fun ext_modesyntax_i x y (prmode, consts) = ext_cnsts no_read true prmode x y consts;
fun ext_modesyntax x y (prmode, consts) = ext_cnsts read_const true prmode x y consts;


(* add type classes *)

fun const_of_class c = c ^ "_class";

fun class_of_const c_class =
  let
    val c = implode (take (size c_class - size "_class", explode c_class));
  in
    if const_of_class c = c_class then c
    else raise TERM ("class_of_const: bad name " ^ quote c_class, [])
  end;


fun ext_classes int sg (syn, tsig, ctab, (path, spaces), data) classes =
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
    ext_consts_i sg
      (map_syntax (Syntax.extend_consts names) syn,
        Type.add_classes (pp sg) classes' tsig, ctab, (path, spaces'), data)
    consts
  end;


(* add to classrel *)

fun ext_classrel int sg (syn, tsig, ctab, (path, spaces), data) pairs =
  let val intrn = if int then map (pairself (intrn_class spaces)) else I in
    (syn, Type.add_classrel (pp sg) (intrn pairs) tsig, ctab, (path, spaces), data)
  end;


(* add translation functions *)

fun ext_trfs ext non_typed sg (syn, tsig, ctab, names, data) (atrs, trs, tr's, atr's) =
  let val syn' = syn |> ext (atrs, trs, map (apsnd non_typed) tr's, atr's)
  in make_syntax sg syn'; (syn', tsig, ctab, names, data) end;

fun ext_trfsT ext sg (syn, tsig, ctab, names, data) tr's =
  let val syn' = syn |> ext ([], [], tr's, [])
  in make_syntax sg syn'; (syn', tsig, ctab, names, data) end;

fun ext_trfuns sg = ext_trfs (map_syntax o Syntax.extend_trfuns) Syntax.non_typed_tr' sg;
fun ext_trfunsT sg = ext_trfsT (map_syntax o Syntax.extend_trfuns) sg;
fun ext_advanced_trfuns sg = ext_trfs extend_trfuns Syntax.non_typed_tr'' sg;
fun ext_advanced_trfunsT sg = ext_trfsT extend_trfuns sg;


(* add token translation functions *)

fun ext_tokentrfuns sg (syn, tsig, ctab, names, data) args =
  (map_syntax (Syntax.extend_tokentrfuns args) syn, tsig, ctab, names, data);


(* add translation rules *)

fun ext_trrules sg (syn, tsig, ctab, (path, spaces), data) args =
  (syn |> map_syntax (Syntax.extend_trrules (is_logtype sg) (make_syntax sg syn)
      (map (Syntax.map_trrule (fn (root, str) => (intrn spaces typeK root, str))) args)),
    tsig, ctab, (path, spaces), data);

fun ext_trrules_i _ (syn, tsig, ctab, names, data) args =
  (syn |> map_syntax (Syntax.extend_trrules_i args), tsig, ctab, names, data);


(* add to path *)

fun ext_path _ (syn, tsig, ctab, (path, spaces), data) elems =
  let
    val path' =
      if elems = "//" then None
      else if elems = "/" then Some []
      else if elems = ".." andalso is_some path andalso path <> Some [] then
        Some (fst (split_last (the path)))
      else Some (if_none path [] @ NameSpace.unpack elems);
  in
    (syn, tsig, ctab, (path', spaces), data)
  end;


(* change name space *)

fun ext_add_space _ (syn, tsig, ctab, (path, spaces), data) (kind, names) =
  (syn, tsig, ctab, (path, add_names spaces kind names), data);

fun ext_hide_space _ (syn, tsig, ctab, (path, spaces), data) (b, (kind, xnames)) =
  (syn, tsig, ctab, (path, hide_names b spaces kind (map (intrn spaces kind) xnames)), data);

fun ext_hide_space_i _ (syn, tsig, ctab, (path, spaces), data) (b, (kind, names)) =
  (syn, tsig, ctab, (path, hide_names b spaces kind names), data);


(* signature data *)

fun ext_init_data sg (syn, tsig, ctab, names, data) (kind, (e, cp, ext, mrg, prt)) =
  (syn, tsig, ctab, names, init_data_sg sg data kind e cp ext mrg prt);

fun ext_put_data sg (syn, tsig, ctab, names, data) (kind, f, x) =
  (syn, tsig, ctab, names, put_data_sg sg data kind f x);


fun copy_data (k, (e, mths as (cp, _, _, _))) =
  (k, (cp e handle exn => err_method "copy" (Object.name_of_kind k) exn, mths));

fun copy (sg as Sg ({id = _, stamps, syn}, {self, tsig, consts, path, spaces, data})) =
  let
    val _ = check_stale sg;
    val self' = SgRef (Some (ref sg));
    val Data tab = data;
    val data' = Data (Symtab.map copy_data tab);
  in create_sign self' stamps "#" (syn, tsig, consts, (path, spaces), data') end;


(* the external interfaces *)

val add_classes          = extend_sign true (ext_classes true) "#";
val add_classes_i        = extend_sign true (ext_classes false) "#";
val add_classrel         = extend_sign true (ext_classrel true) "#";
val add_classrel_i       = extend_sign true (ext_classrel false) "#";
val add_defsort          = extend_sign true ext_defsort "#";
val add_defsort_i        = extend_sign true ext_defsort_i "#";
val add_types            = extend_sign true ext_types "#";
val add_nonterminals     = extend_sign true ext_nonterminals "#";
val add_tyabbrs          = extend_sign true ext_tyabbrs "#";
val add_tyabbrs_i        = extend_sign true ext_tyabbrs_i "#";
val add_arities          = extend_sign true ext_arities "#";
val add_arities_i        = extend_sign true ext_arities_i "#";
val add_consts           = extend_sign true ext_consts "#";
val add_consts_i         = extend_sign true ext_consts_i "#";
val add_syntax           = extend_sign true ext_syntax "#";
val add_syntax_i         = extend_sign true ext_syntax_i "#";
val add_modesyntax       = extend_sign true ext_modesyntax "#";
val add_modesyntax_i     = extend_sign true ext_modesyntax_i "#";
val add_trfuns           = extend_sign true ext_trfuns "#";
val add_trfunsT          = extend_sign true ext_trfunsT "#";
val add_advanced_trfuns  = extend_sign true ext_advanced_trfuns "#";
val add_advanced_trfunsT = extend_sign true ext_advanced_trfunsT "#";
val add_tokentrfuns      = extend_sign true ext_tokentrfuns "#";
val add_trrules          = extend_sign true ext_trrules "#";
val add_trrules_i        = extend_sign true ext_trrules_i "#";
val add_path             = extend_sign true ext_path "#";
val add_space            = extend_sign true ext_add_space "#";
val hide_space           = curry (extend_sign true ext_hide_space "#");
val hide_space_i         = curry (extend_sign true ext_hide_space_i "#");
val init_data            = extend_sign true ext_init_data "#";
fun put_data k f x       = extend_sign true ext_put_data "#" (k, f, x);
fun add_name name        = extend_sign true (K K) name ();
val prep_ext             = extend_sign false (K K) "#" ();



(** merge signatures **)        (*exception TERM*)

(* merge_stamps *)

fun merge_stamps stamps1 stamps2 =
  let val stamps = merge_lists' stamps1 stamps2 in
    (case duplicates (map ! stamps) of
      [] => stamps
    | dups => raise TERM ("Attempt to merge different versions of theories "
        ^ commas_quote dups, []))
  end;


(* trivial merge *)

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


(* non-trivial merge *)              (*exception TERM/ERROR*)

fun nontriv_merge (sg1, sg2) =
  if subsig (sg2, sg1) then sg1
  else if subsig (sg1, sg2) then sg2
  else if is_draft sg1 orelse is_draft sg2 then
    raise TERM ("Attempt to merge draft signatures", [])
  else if exists_stamp PureN sg1 andalso exists_stamp CPureN sg2 orelse
      exists_stamp CPureN sg1 andalso exists_stamp PureN sg2 then
    raise TERM ("Cannot merge Pure and CPure signatures", [])
  else
    let
      val Sg ({id = _, stamps = stamps1, syn = Syn (syntax1, trfuns1)},
          {self = _, tsig = tsig1, consts = consts1,
            path = _, spaces = spaces1, data = data1}) = sg1;
      val Sg ({id = _, stamps = stamps2, syn = Syn (syntax2, trfuns2)},
          {self = _, tsig = tsig2, consts = consts2,
            path = _, spaces = spaces2, data = data2}) = sg2;

      val stamps = merge_stamps stamps1 stamps2;
      val syntax = Syntax.merge_syntaxes syntax1 syntax2;
      val trfuns = merge_trfuns trfuns1 trfuns2;
      val consts = Symtab.merge eq_snd (consts1, consts2)
        handle Symtab.DUPS cs => err_dup_consts cs;

      val path = Some [];
      val kinds = distinct (map fst (spaces1 @ spaces2));
      val spaces =
        kinds ~~
          ListPair.map NameSpace.merge
            (map (space_of spaces1) kinds, map (space_of spaces2) kinds);

      val data = merge_data (data1, data2);

      val pre_sign = make_sign (ref "", SgRef (Some (ref dummy_sg)),
        tsig1, consts, Syn (syntax, trfuns), path, spaces, data, ref "#" :: stamps1);
      val tsig = Type.merge_tsigs (pp pre_sign) (tsig1, tsig2);

      val self_ref = ref dummy_sg;
      val self = SgRef (Some self_ref);
      val sign = make_sign (ref "", self, tsig, consts, Syn (syntax, trfuns),
        path, spaces, data, stamps);
    in self_ref := sign; syn_of sign; sign end;

end;
