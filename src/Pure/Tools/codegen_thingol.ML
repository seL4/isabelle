(*  Title:      Pure/Tools/codegen_thingol.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Intermediate language ("Thin-gol") for code extraction.
*)

infix 8 `%%;
infixr 6 `->;
infixr 6 `-->;
infix 4 `$;
infix 4 `$$;
infixr 3 `|->;
infixr 3 `|-->;

signature BASIC_CODEGEN_THINGOL =
sig
  type vname = string;
  type sortcontext = ClassPackage.sortcontext;
  datatype iclasslookup =
      Instance of string * iclasslookup list list
    | Lookup of class list * (vname * int);
  datatype itype =
      `%% of string * itype list
    | `-> of itype * itype
    | ITyVar of vname;
  datatype iterm =
      IConst of string * (iclasslookup list list * itype)
    | IVar of vname
    | `$ of iterm * iterm
    | `|-> of (vname * itype) * iterm
    | INum of IntInf.int (*non-negative!*) * iterm
    | IChar of string (*length one!*) * iterm
    | ICase of ((iterm * itype) * (iterm * iterm) list) * iterm;
        (*((discrimendum expression (de), discrimendum type (dty)),
                [(selector expression (se), body expression (be))]),
                native expression (e0))*)
end;

signature CODEGEN_THINGOL =
sig
  include BASIC_CODEGEN_THINGOL;
  val `--> : itype list * itype -> itype;
  val `$$ : iterm * iterm list -> iterm;
  val `|--> : (vname * itype) list * iterm -> iterm;
  val pretty_itype: itype -> Pretty.T;
  val pretty_iterm: iterm -> Pretty.T;
  val unfoldl: ('a -> ('a * 'b) option) -> 'a -> 'a * 'b list;
  val unfoldr: ('a -> ('b * 'a) option) -> 'a -> 'b list * 'a;
  val unfold_fun: itype -> itype list * itype;
  val unfold_app: iterm -> iterm * iterm list;
  val unfold_abs: iterm -> (iterm * itype) list * iterm;
  val unfold_let: iterm -> ((iterm * itype) * iterm) list * iterm;
  val unfold_const_app: iterm ->
    ((string * (iclasslookup list list * itype)) * iterm list) option;
  val add_constnames: iterm -> string list -> string list;
  val add_varnames: iterm -> string list -> string list;
  val is_pat: (string -> bool) -> iterm -> bool;
  val vars_distinct: iterm list -> bool;
  val map_pure: (iterm -> 'a) -> iterm -> 'a;
  val eta_expand: (string * (iclasslookup list list * itype)) * iterm list -> int -> iterm;
  val resolve_tycos: (string -> string) -> itype * iterm list -> itype * iterm list;
  val resolve_consts: (string -> string) -> iterm -> iterm;

  type funn = (iterm list * iterm) list * (sortcontext * itype);
  type datatyp = sortcontext * (string * itype list) list;
  datatype def =
      Bot
    | Fun of funn
    | Typesyn of sortcontext * itype
    | Datatype of datatyp
    | Datatypecons of string
    | Class of class list * (vname * (string * (sortcontext * itype)) list)
    | Classmember of class
    | Classinst of (class * (string * (vname * sort) list))
          * ((class * iclasslookup list) list
        * (string * iterm) list);
  type module;
  type transact;
  type 'dst transact_fin;
  val pretty_def: def -> Pretty.T;
  val pretty_module: module -> Pretty.T;
  val pretty_deps: module -> Pretty.T;
  val empty_module: module;
  val get_def: module -> string -> def;
  val merge_module: module * module -> module;
  val diff_module: module * module -> (string * def) list;
  val project_module: string list -> module -> module;
  val purge_module: string list -> module -> module;
(*   val flat_funs_datatypes: module -> (string * def) list;  *)
  val add_eval_def: string (*shallow name space*) * iterm -> module -> string * module;
  val delete_garbage: string list (*hidden definitions*) -> module -> module;
  val has_nsp: string -> string -> bool;
  val ensure_def: (string -> transact -> def transact_fin) -> bool -> string
    -> string -> transact -> transact;
  val succeed: 'a -> transact -> 'a transact_fin;
  val fail: string -> transact -> 'a transact_fin;
  val message: string -> (transact -> 'a) -> transact -> 'a;
  val start_transact: string option -> (transact -> 'a * transact) -> module -> 'a * module;
  val elim_classes: module -> funn -> (iterm list * iterm) list * itype;

  val debug: bool ref;
  val debug_msg: ('a -> string) -> 'a -> 'a;
  val soft_exc: bool ref;

  val serialize:
    ((string -> string -> string) -> string -> (string * def) list -> 'a option)
    -> ((string -> string) -> string list -> (string * string) * 'a list -> 'a option)
    -> (string -> string option)
    -> (string * string -> string)
    -> string list list -> string -> module -> 'a option;
end;

structure CodegenThingol: CODEGEN_THINGOL =
struct

(** auxiliary **)

val debug = ref false;
fun debug_msg f x = (if !debug then Output.tracing (f x) else (); x);
val soft_exc = ref true;

fun unfoldl dest x =
  case dest x
   of NONE => (x, [])
    | SOME (x1, x2) =>
        let val (x', xs') = unfoldl dest x1 in (x', xs' @ [x2]) end;

fun unfoldr dest x =
  case dest x
   of NONE => ([], x)
    | SOME (x1, x2) =>
        let val (xs', x') = unfoldr dest x2 in (x1::xs', x') end;



(** language core - types, pattern, expressions **)

(* language representation *)

type vname = string;

type sortcontext = ClassPackage.sortcontext;
datatype iclasslookup =
    Instance of string * iclasslookup list list
  | Lookup of class list * (vname * int);

datatype itype =
    `%% of string * itype list
  | `-> of itype * itype
  | ITyVar of vname;

datatype iterm =
    IConst of string * (iclasslookup list list * itype)
  | IVar of vname
  | `$ of iterm * iterm
  | `|-> of (vname * itype) * iterm
  | INum of IntInf.int * iterm
  | IChar of string * iterm
  | ICase of ((iterm * itype) * (iterm * iterm) list) * iterm;
    (*see also signature*)

(*
  variable naming conventions

  bare names:
    variable names          v
    class names             cls
    type constructor names  tyco
    datatype names          dtco
    const names (general)   c
    constructor names       co
    class member names      m
    arbitrary name          s

  constructs:
    sort                    sort
    type                    ty
    expression              e
    pattern                 p, pat
    instance (cls, tyco)    inst
    variable (v, ty)        var
    class member (m, ty)    membr
    constructors (co, tys)  constr
 *)

val op `--> = Library.foldr (op `->);
val op `$$ = Library.foldl (op `$);
val op `|--> = Library.foldr (op `|->);

val pretty_sortcontext =
  Pretty.list "(" ")" o Pretty.commas o map (fn (v, sort) => (Pretty.block o Pretty.breaks)
    [Pretty.str v, Pretty.str "::", Pretty.enum "&" "" "" (map Pretty.str sort)]);

fun pretty_itype (tyco `%% tys) =
      Pretty.enum "" "(" ")" (Pretty.str tyco :: map pretty_itype tys)
  | pretty_itype (ty1 `-> ty2) =
      Pretty.enum "" "(" ")" [pretty_itype ty1, Pretty.str "->", pretty_itype ty2]
  | pretty_itype (ITyVar v) =
      Pretty.str v;

fun pretty_iterm (IConst (c, _)) =
      Pretty.str c
  | pretty_iterm (IVar v) =
      Pretty.str ("?" ^ v)
  | pretty_iterm (e1 `$ e2) =
      (Pretty.enclose "(" ")" o Pretty.breaks)
        [pretty_iterm e1, pretty_iterm e2]
  | pretty_iterm ((v, ty) `|-> e) =
      (Pretty.enclose "(" ")" o Pretty.breaks)
        [Pretty.str v, Pretty.str "::", pretty_itype ty, Pretty.str "|->", pretty_iterm e]
  | pretty_iterm (INum (n, _)) =
      (Pretty.str o IntInf.toString) n
  | pretty_iterm (IChar (c, _)) =
      (Pretty.str o quote) c
  | pretty_iterm (ICase (((e, _), cs), _)) =
      (Pretty.enclose "(" ")" o Pretty.breaks) [
        Pretty.str "case",
        pretty_iterm e,
        Pretty.enclose "(" ")" (map (fn (p, e) =>
          (Pretty.block o Pretty.breaks) [
            pretty_iterm p,
            Pretty.str "=>",
            pretty_iterm e
          ]
        ) cs)
      ];

val unfold_fun = unfoldr
  (fn op `-> t => SOME t
    | _ => NONE);

val unfold_app = unfoldl
  (fn op `$ e => SOME e
    | _ => NONE);

val unfold_abs = unfoldr
  (fn (v, ty) `|-> (e as ICase (((IVar w, _), [(se, be)]), _)) =>
        if v = w then SOME ((se, ty), be) else SOME ((IVar v, ty), e)
    | (v, ty) `|-> e => SOME ((IVar v, ty), e)
    | _ => NONE)

val unfold_let = unfoldr
  (fn ICase (((de, dty), [(se, be)]), _) => SOME (((se, dty), de), be)
    | _ => NONE);

fun unfold_const_app e =
 case unfold_app e
  of (IConst x, es) => SOME (x, es)
   | _ => NONE;

fun map_itype _ (ty as ITyVar _) =
      ty
  | map_itype f (tyco `%% tys) =
      tyco `%% map f tys
  | map_itype f (t1 `-> t2) =
      f t1 `-> f t2;

fun eq_ityp ((sctxt1, ty1), (sctxt2, ty2)) =
  let
    exception NO_MATCH;
    fun eq_sctxt subs sctxt1 sctxt2 =
      map (fn (v : string, sort : string list) => case AList.lookup (op =) subs v
       of NONE => raise NO_MATCH
        | SOME (v' : string) => case AList.lookup (op =) sctxt2 v'
           of NONE => raise NO_MATCH
            | SOME sort' => if sort <> sort' then raise NO_MATCH else ()) sctxt1
    fun eq (ITyVar v1) (ITyVar v2) subs =
          (case AList.lookup (op =) subs v1
           of NONE => subs |> AList.update (op =) (v1, v2)
            | SOME v1' =>
                if v1' <> v2
                then raise NO_MATCH
                else subs)
      | eq (tyco1 `%% tys1) (tyco2 `%% tys2) subs =
          if tyco1 <> tyco2
          then raise NO_MATCH
          else subs |> fold2 eq tys1 tys2
      | eq (ty11 `-> ty12) (ty21 `-> ty22) subs =
          subs |> eq ty11 ty21 |> eq ty12 ty22
      | eq _ _ _ = raise NO_MATCH;
  in
    (eq ty1 ty2 []; true)
    handle NO_MATCH => false
  end;

fun instant_itype f =
  let
    fun instant (ITyVar x) = f x
      | instant y = map_itype instant y;
  in instant end;

fun is_pat is_cons (e as IConst (c, ([], _))) = is_cons  c
  | is_pat _ (e as IVar _) = true
  | is_pat is_cons (e as (e1 `$ e2)) =
      is_pat is_cons e1 andalso is_pat is_cons e2
  | is_pat _ (e as INum _) = true
  | is_pat _ (e as IChar _) = true
  | is_pat _ _ = false;

fun map_pure f (e as IConst _) =
      f e
  | map_pure f (e as IVar _) =
      f e
  | map_pure f (e as _ `$ _) =
      f e
  | map_pure f (e as _ `|-> _) =
      f e
  | map_pure f (INum (_, e0)) =
      f e0
  | map_pure f (IChar (_, e0)) =
      f e0
  | map_pure f (ICase (_, e0)) =
      f e0;

fun resolve_tycos _ = error "";
fun resolve_consts _ = error "";

fun add_constnames (IConst (c, _)) =
      insert (op =) c
  | add_constnames (IVar _) =
      I
  | add_constnames (e1 `$ e2) =
      add_constnames e1 #> add_constnames e2
  | add_constnames (_ `|-> e) =
      add_constnames e
  | add_constnames (INum (_, e)) =
      add_constnames e
  | add_constnames (IChar (_, e)) =
      add_constnames e
  | add_constnames (ICase (_, e)) =
      add_constnames e;

fun add_varnames (IConst _) =
      I
  | add_varnames (IVar v) =
      insert (op =) v
  | add_varnames (e1 `$ e2) =
      add_varnames e1 #> add_varnames e2
  | add_varnames ((v, _) `|-> e) =
      insert (op =) v #> add_varnames e
  | add_varnames (INum (_, e)) =
      add_varnames e
  | add_varnames (IChar (_, e)) =
      add_varnames e
  | add_varnames (ICase (((de, _), bses), _)) =
      add_varnames de #> fold (fn (be, se) => add_varnames be #> add_varnames se) bses;

fun vars_distinct es =
  let
    fun distinct _ NONE =
          NONE
      | distinct (IConst _) x =
          x
      | distinct (IVar v) (SOME vs) =
          if member (op =) vs v then NONE else SOME (v::vs)
      | distinct (e1 `$ e2) x =
          x |> distinct e1 |> distinct e2
      | distinct (_ `|-> e) x =
          x |> distinct e
      | distinct (INum _) x =
          x
      | distinct (IChar _) x =
          x
      | distinct (ICase (((de, _), bses), _)) x =
          x |> distinct de |> fold (fn (be, se) => distinct be #> distinct se) bses;
  in is_some (fold distinct es (SOME [])) end;

fun eta_expand (c as (_, (_, ty)), es) k =
  let
    val j = length es;
    val l = k - j;
    val tys = (curry Library.take l o curry Library.drop j o fst o unfold_fun) ty;
    val vs_tys = Name.names (fold Name.declare (fold add_varnames es []) Name.context) "a" tys;
  in vs_tys `|--> IConst c `$$ es @ map (fn (v, _) => IVar v) vs_tys end;



(** language module system - definitions, modules, transactions **)

(* type definitions *)

type funn = (iterm list * iterm) list * (sortcontext * itype);
type datatyp = sortcontext * (string * itype list) list;

datatype def =
    Bot
  | Fun of funn
  | Typesyn of sortcontext * itype
  | Datatype of datatyp
  | Datatypecons of string
  | Class of class list * (vname * (string * (sortcontext * itype)) list)
  | Classmember of class
  | Classinst of (class * (string * (vname * sort) list))
          * ((class * iclasslookup list) list
        * (string * iterm) list);

datatype node = Def of def | Module of node Graph.T;
type module = node Graph.T;
type transact = Graph.key option * module;
type 'dst transact_fin = 'dst * module;
exception FAIL of string list * exn option;

val eq_def = (op =) : def * def -> bool;

(* simple diagnosis *)

fun pretty_def Bot =
      Pretty.str "<Bot>"
  | pretty_def (Fun (eqs, (sortctxt, ty))) =
      Pretty.enum " |" "" "" (
        map (fn (ps, body) =>
          Pretty.block [
            Pretty.enum "," "[" "]" (map pretty_iterm ps),
            Pretty.str " |->",
            Pretty.brk 1,
            pretty_iterm body,
            Pretty.str "::",
            pretty_sortcontext sortctxt,
            Pretty.str "/",
            pretty_itype ty
          ]) eqs
        )
  | pretty_def (Typesyn (vs, ty)) =
      Pretty.block [
        pretty_sortcontext vs,
        Pretty.str " |=> ",
        pretty_itype ty
      ]
  | pretty_def (Datatype (vs, cs)) =
      Pretty.block [
        pretty_sortcontext vs,
        Pretty.str " |=> ",
        Pretty.enum " |" "" ""
          (map (fn (c, tys) => (Pretty.block o Pretty.breaks)
            (Pretty.str c :: map pretty_itype tys)) cs)
      ]
  | pretty_def (Datatypecons dtname) =
      Pretty.str ("cons " ^ dtname)
  | pretty_def (Class (supcls, (v, mems))) =
      Pretty.block [
        Pretty.str ("class var " ^ v ^ " extending "),
        Pretty.enum "," "[" "]" (map Pretty.str supcls),
        Pretty.str " with ",
        Pretty.enum "," "[" "]"
          (map (fn (m, (_, ty)) => Pretty.block
            [Pretty.str (m ^ "::"), pretty_itype ty]) mems)
      ]
  | pretty_def (Classmember clsname) =
      Pretty.block [
        Pretty.str "class member belonging to ",
        Pretty.str clsname
      ]
  | pretty_def (Classinst ((clsname, (tyco, arity)), _)) =
      Pretty.block [
        Pretty.str "class instance (",
        Pretty.str clsname,
        Pretty.str ", (",
        Pretty.str tyco,
        Pretty.str ", ",
        Pretty.enum "," "[" "]" (map (Pretty.enum "," "{" "}" o
          map Pretty.str o snd) arity),
        Pretty.str "))"
      ];

fun pretty_module modl =
  let
    fun pretty (name, Module modl) =
          Pretty.block (
            Pretty.str ("module " ^ name ^ " {")
            :: Pretty.brk 1
            :: Pretty.chunks (map pretty (AList.make (Graph.get_node modl)
                 (Graph.strong_conn modl |> flat |> rev)))
            :: Pretty.str "}" :: nil
          )
      | pretty (name, Def def) =
          Pretty.block [Pretty.str name, Pretty.str " :=", Pretty.brk 1, pretty_def def]
  in pretty ("//", Module modl) end;

fun pretty_deps modl =
  let
    fun one_node key =
      let
        val preds_ = Graph.imm_preds modl key;
        val succs_ = Graph.imm_succs modl key;
        val mutbs = gen_inter (op =) (preds_, succs_);
        val preds = subtract (op =) mutbs preds_;
        val succs = subtract (op =) mutbs succs_;
      in
        (Pretty.block o Pretty.fbreaks) (
          Pretty.str key
          :: map (fn s => Pretty.str ("<-> " ^ s)) mutbs
          @ map (fn s => Pretty.str ("<-- " ^ s)) preds
          @ map (fn s => Pretty.str ("--> " ^ s)) succs
          @ (the_list oo Option.mapPartial)
            ((fn Module modl' => SOME (pretty_deps modl')
               | _ => NONE) o Graph.get_node modl) (SOME key)
        )
      end
  in
    modl
    |> Graph.strong_conn
    |> flat
    |> rev
    |> map one_node
    |> Pretty.chunks
  end;


(* name handling *)

fun dest_name name =
  let
    val name' = NameSpace.unpack name
    val (name'', name_base) = split_last name'
    val (modl, shallow) = split_last name''
  in (modl, NameSpace.pack [shallow, name_base]) end
  handle Empty => error ("Not a qualified name: " ^ quote name);

fun has_nsp name shallow =
  NameSpace.is_qualified name
  andalso let
    val name' = NameSpace.unpack name
    val (name'', _) = split_last name'
    val (_, shallow') = split_last name''
  in shallow' = shallow end;

fun dest_modl (Module m) = m;
fun dest_def (Def d) = d;


(* modules *)

val empty_module = Graph.empty; (*read: "depends on"*)

fun get_def modl name =
  case dest_name name
   of (modlname, base) =>
        let
          fun get (Module node) [] =
                (dest_def o Graph.get_node node) base
            | get (Module node) (m::ms) =
                get (Graph.get_node node m) ms
        in get (Module modl) modlname end;

fun is_def modl name =
  case try (get_def modl) name
   of NONE => false
    | SOME Bot => false
    | _ => true;

fun add_def (name, def) =
  let
    val (modl, base) = dest_name name;
    fun add [] =
          Graph.new_node (base, Def def)
      | add (m::ms) =
          Graph.default_node (m, Module empty_module)
          #> Graph.map_node m (Module o add ms o dest_modl)
  in add modl end;

fun map_def name f =
  let
    val (modl, base) = dest_name name;
    fun mapp [] =
          Graph.map_node base (Def o f o dest_def)
      | mapp (m::ms) =
          Graph.map_node m (Module o mapp ms o dest_modl)
  in mapp modl end;

fun ensure_bot name =
  let
    val (modl, base) = dest_name name;
    fun ensure [] module =
          (case try (Graph.get_node module) base
           of NONE =>
                module
                |> Graph.new_node (base, Def Bot)
            | SOME (Module _) => error ("Module already present: " ^ quote name)
            | _ => module)
      | ensure (m::ms) module =
          module
          |> Graph.default_node (m, Module empty_module)
          |> Graph.map_node m (Module o ensure ms o dest_modl)
  in ensure modl end;

fun add_def_incr strict (name, Bot) module =
      (case try (get_def module) name
       of NONE => if strict then error "Attempted to add Bot to module"
            else map_def name (K Bot) module
        | SOME Bot => if strict then error "Attempted to add Bot to module"
            else map_def name (K Bot) module
        | SOME _ => module)
  | add_def_incr _ (name, def) module =
      (case try (get_def module) name
       of NONE => add_def (name, def) module
        | SOME Bot => map_def name (K def) module
        | SOME def' => if eq_def (def, def')
            then module
            else error ("Tried to overwrite definition " ^ quote name));

fun add_dep (name1, name2) modl =
  if name1 = name2 then modl
  else
    let
      val m1 = dest_name name1 |> apsnd single |> (op @);
      val m2 = dest_name name2 |> apsnd single |> (op @);
      val (ms, (r1, r2)) = chop_prefix (op =) (m1, m2);
      val (ms, (s1::r1, s2::r2)) = chop_prefix (op =) (m1, m2);
      val add_edge =
        if null r1 andalso null r2
        then Graph.add_edge
        else fn edge => fn gr => (Graph.add_edge_acyclic edge gr
          handle Graph.CYCLES _ =>
            error ("Adding dependency "
              ^ quote name1 ^ " -> " ^ quote name2 ^ " would result in module dependency cycle"))
      fun add [] node =
            node
            |> add_edge (s1, s2)
        | add (m::ms) node =
            node
            |> Graph.map_node m (Module o add ms o dest_modl);
    in add ms modl end;

fun merge_module modl12 =
  let
    fun join_module _ (Module m1, Module m2) =
          Module (merge_module (m1, m2))
      | join_module name (Def d1, Def d2) =
          if eq_def (d1, d2) then Def d1 else Def Bot
      | join_module name _ = raise Graph.DUP name
  in Graph.join join_module modl12 end;

fun diff_module modl12 =
  let
    fun diff_entry prefix modl2 (name, Def def1) =
          let
            val e2 = try (Graph.get_node modl2) name
          in if is_some e2 andalso eq_def (def1, (dest_def o the) e2)
            then I
            else cons (NameSpace.pack (prefix @ [name]), def1)
          end
      | diff_entry prefix modl2 (name, Module modl1) =
          diff_modl (prefix @ [name]) (modl1,
            (the_default empty_module o Option.map dest_modl o try (Graph.get_node modl2)) name)
    and diff_modl prefix (modl1, modl2) =
      fold (diff_entry prefix modl2)
        ((AList.make (Graph.get_node modl1) o flat o Graph.strong_conn) modl1)
  in diff_modl [] modl12 [] end;

fun project_module names modl =
  let
    datatype pathnode = PN of (string list * (string * pathnode) list);
    fun mk_ipath ([], base) (PN (defs, modls)) =
          PN (base :: defs, modls)
      | mk_ipath (n::ns, base) (PN (defs, modls)) =
          modls
          |> AList.default (op =) (n, PN ([], []))
          |> AList.map_entry (op =) n (mk_ipath (ns, base))
          |> (pair defs #> PN);
    fun select (PN (defs, modls)) (Module module) =
      module
      |> Graph.project (member (op =) ((*!*) Graph.all_succs module (defs @ map fst modls)))
      |> fold (fn (name, modls) => Graph.map_node name (select modls)) modls
      |> Module;
  in
    Module modl
    |> select (fold (mk_ipath o dest_name)
         (filter NameSpace.is_qualified names) (PN ([], [])))
    |> dest_modl
  end;

fun purge_module names modl =
  let
    fun split_names names =
      fold
        (fn ([], name) => apfst (cons name)
          | (m::ms, name) => apsnd (AList.default (op =) (m : string, [])
              #> AList.map_entry (op =) m (cons (ms, name))))
        names ([], []);
    fun purge names (Module modl) =
      let
        val (ndefs, nmodls) = split_names names;
      in
        modl
        |> Graph.del_nodes (Graph.all_preds modl ndefs)
        |> Graph.del_nodes ndefs
        |> Graph.del_nodes (Graph.all_preds modl (map fst nmodls))
        |> fold (fn (nmodl, names') => Graph.map_node nmodl (purge names')) nmodls
        |> Module
      end;
  in
    Module modl
    |> purge (map dest_name names)
    |> dest_modl
  end;

fun flat_module modl =
  maps (
   fn (name, Module modl) => map (apfst (NameSpace.append name)) (flat_module modl)
    | (name, Def def) => [(name, def)]
  ) ((AList.make (Graph.get_node modl) o flat o Graph.strong_conn) modl)

(*
fun flat_funs_datatypes modl =
  map (
   fn def as (_, Datatype _) => def
    | (name, Fun (eqs, (sctxt, ty))) => let
          val vs = fold (fn (rhs, lhs) => fold add_varnames rhs #> add_varnames lhs) eqs [];
          fun fold_map_snd f (x, ys) = fold_map f ys #-> (fn zs => pair (x, zs));
          fun all_ops_of class = [] : (class * (string * itype) list) list
            (*FIXME; itype within current context*);
          fun name_ops class = 
            (fold_map o fold_map_snd)
              (fn (c, ty) => Name.variants [c] #-> (fn [v] => pair (c, (ty, v)))) (all_ops_of class);
          (*FIXME: should contain superclasses only once*)
          val (octxt, _) = (fold_map o fold_map_snd) name_ops sctxt
            (Name.make_context vs);
          (* --> (iterm * itype) list *)
          fun flat_classlookup (Instance (inst, lss)) =
                (case get_def modl inst
                 of (Classinst (_, (suparities, ops)))
                      => maps (maps flat_classlookup o snd) suparities @ map (apsnd flat_iterm) ops
                  | _ => error ("Bad instance: " ^ quote inst))
            | flat_classlookup (Lookup (classes, (v, k))) =
                let
                  val parm_map = nth ((the o AList.lookup (op =) octxt) v)
                    (if k = ~1 then 0 else k);
                in map (apfst IVar o swap o snd) (case classes
                 of class::_ => (the o AList.lookup (op =) parm_map) class
                  | _ => (snd o hd) parm_map)
                end
          and flat_iterm (e as IConst (c, (lss, ty))) =
                let
                  val (es, tys) = split_list ((maps o maps) flat_classlookup lss)
                in IConst (c, ([], tys `--> ty)) `$$ es end
                (*FIXME Eliminierung von Projektionen*)
            | flat_iterm (e as IVar _) =
                e
            | flat_iterm (e1 `$ e2) =
                flat_iterm e1 `$ flat_iterm e2
            | flat_iterm (v_ty `|-> e) =
                v_ty `|-> flat_iterm e
            | flat_iterm (INum (k, e)) =
                INum (k, flat_iterm e)
            | flat_iterm (IChar (s, e)) =
                IChar (s, flat_iterm e)
            | flat_iterm (ICase (((de, dty), es), e)) =
                ICase (((flat_iterm de, dty), map (pairself flat_iterm) es), flat_iterm e);
        in
          (name, Fun (map (fn (lhs, rhs) => (map flat_iterm lhs, flat_iterm rhs)) eqs,
            ([], maps ((maps o maps) (map (fst o snd) o snd) o snd) octxt `--> ty)))
        end
  ) (flat_module modl);
*)

val add_deps_of_sortctxt =
  fold (fn (v : vname, sort : sort) => fold (insert (op =)) sort);

fun add_deps_of_classlookup (Instance (tyco, lss)) =
      insert (op =) tyco
      #> (fold o fold) add_deps_of_classlookup lss
  | add_deps_of_classlookup (Lookup (clss, _)) =
      fold (insert (op =)) clss;

fun add_deps_of_type (tyco `%% tys) =
      insert (op =) tyco
      #> fold add_deps_of_type tys
  | add_deps_of_type  (ty1 `-> ty2) =
      add_deps_of_type ty1
      #> add_deps_of_type ty2
  | add_deps_of_type (ITyVar v) =
      I;

fun add_deps_of_term (IConst (c, (lss, ty))) =
      insert (op =) c
      #> add_deps_of_type ty
      #> (fold o fold) add_deps_of_classlookup lss
  | add_deps_of_term (IVar _) =
      I
  | add_deps_of_term (e1 `$ e2) =
      add_deps_of_term e1 #> add_deps_of_term e2
  | add_deps_of_term ((_, ty) `|-> e) =
      add_deps_of_type ty
      #> add_deps_of_term e
  | add_deps_of_term (INum _) =
      I
  | add_deps_of_term (IChar (_, e)) =
      add_deps_of_term e
  | add_deps_of_term (ICase (_, e)) =
      add_deps_of_term e;

fun deps_of Bot =
      []
  | deps_of (Fun (eqs, (sctxt, ty))) =
      []
      |> add_deps_of_sortctxt sctxt
      |> add_deps_of_type ty
      |> fold (fn (lhs, rhs) => fold add_deps_of_term lhs #> add_deps_of_term rhs) eqs
  | deps_of (Typesyn (sctxt, ty)) =
      []
      |> add_deps_of_sortctxt sctxt
      |> add_deps_of_type ty
  | deps_of (Datatype (sctxt, cos)) =
      []
      |> add_deps_of_sortctxt sctxt
      |> fold (fn (c, tys) => insert (op =) c #> fold add_deps_of_type tys) cos
  | deps_of (Datatypecons dtco) =
      [dtco]
  | deps_of (Class (supclss, (_, memdecls))) =
      []
      |> fold (insert (op =)) supclss
      |> fold (fn (name, (sctxt, ty)) =>
            insert (op =) name
            #> add_deps_of_sortctxt sctxt
            #> add_deps_of_type ty
      ) memdecls
  | deps_of (Classmember class) =
      [class]
  | deps_of (Classinst ((class, (tyco, sctxt)), (suparities, memdefs))) =
      []
      |> insert (op =) class
      |> insert (op =) tyco
      |> add_deps_of_sortctxt sctxt
      |> fold (fn (supclass, ls) =>
            insert (op =) supclass
            #> fold add_deps_of_classlookup ls
      ) suparities
      |> fold (fn (name, e) =>
            insert (op =) name
            #> add_deps_of_term e
      ) memdefs;

fun delete_garbage hidden modl =
  let
    fun allnames modl =
      let
        val entries = AList.make (Graph.get_node modl) (Graph.keys modl)
        fun is_def (name, Module _) = NONE
          | is_def (name, _) = SOME name;
        fun is_modl (name, Module modl) = SOME (name, modl)
          | is_modl (name, _) = NONE;
        val defs = map_filter is_def entries;
        val modls = map_filter is_modl entries;
      in
        defs
        @ maps (fn (name, modl) => map (NameSpace.append name) (allnames modl)) modls
      end;
    fun alldeps modl =
      let
        val entries = AList.make (Graph.get_node modl) (Graph.keys modl)
        fun is_def (name, Module _) = NONE
          | is_def (name, _) = SOME name;
        fun is_modl (name, Module modl) = SOME (name, modl)
          | is_modl (name, _) = NONE;
        val defs = map_filter is_def entries;
        val modls = map_filter is_modl entries;
      in
        maps (fn name => map (pair (name)) (Graph.imm_succs modl name)) defs
        @ maps (fn (name, modl) => (map o pairself) (NameSpace.append name) (alldeps modl)) modls
      end;
    val names = subtract (op =) hidden (allnames modl);
(*     val _ = writeln "HIDDEN";  *)
(*     val _ = (writeln o commas) hidden;  *)
(*     val _ = writeln "NAMES";  *)
(*     val _ = (writeln o commas) names;  *)
    fun is_bot name =
      case get_def modl name of Bot => true | _ => false;
    val bots = filter is_bot names;
    val defs = filter (not o is_bot) names;
    val expldeps =
      Graph.empty
      |> fold (fn name => Graph.new_node (name, ())) names
      |> fold (fn name => fold (curry Graph.add_edge name)
            (deps_of (get_def modl name) |> subtract (op =) hidden)) names
    val bots' = fold (insert op =) bots (Graph.all_preds expldeps bots);
    val selected = subtract (op =) bots' names;
(*     val deps = filter (fn (x, y) => member (op =) selected x andalso member (op =) selected y)  *)
    val adddeps = maps (fn (n, ns) => map (pair n) ns) (expldeps |> Graph.del_nodes bots' |> Graph.dest);
(*    val _ = writeln "SELECTED";
    val _ = (writeln o commas) selected;
    val _ = writeln "DEPS";
    val _ = (writeln o cat_lines o map (fn (x, y) => x ^ " -> " ^ y)) adddeps; *)
  in
    empty_module
    |> fold (fn name => add_def (name, get_def modl name)) selected
(*     |> fold ensure_bot (hidden @ bots')  *)
    |> fold (fn (x, y) => ((*writeln ("adding " ^ x ^ " -> " ^ y);*) add_dep (x, y))) adddeps
  end;

fun allimports_of modl =
  let
    fun imps_of prfx (Module modl) imps tab =
          let
            val this = NameSpace.pack prfx;
            val name_con = (rev o Graph.strong_conn) modl;
          in
            tab
            |> pair []
            |> fold (fn names => fn (imps', tab) =>
                tab
                |> fold_map (fn name =>
                     imps_of (prfx @ [name]) (Graph.get_node modl name) (imps' @ imps)) names
                |-> (fn imps'' => pair (flat imps'' @ imps'))) name_con
            |-> (fn imps' =>
               Symtab.update_new (this, imps' @ imps)
            #> pair (this :: imps'))
          end
      | imps_of prfx (Def _) imps tab =
          ([], tab);
  in snd (imps_of [] (Module modl) [] Symtab.empty) end;

fun check_samemodule names =
  fold (fn name =>
    let
      val modn = (fst o dest_name) name
    in
     fn NONE => SOME modn
      | SOME mod' => if modn = mod' then SOME modn
          else error ("Inconsistent name prefix for simultanous names: " ^ commas_quote names)
    end
  ) names NONE;

fun check_funeqs eqs =
  (fold (fn (pats, _) =>
    let
      val l = length pats
    in
     fn NONE => SOME l
      | SOME l' => if l = l' then SOME l
          else error "Function definition with different number of arguments"
    end
  ) eqs NONE; eqs);

fun check_prep_def modl Bot =
      Bot
  | check_prep_def modl (Fun (eqs, d)) =
      Fun (check_funeqs eqs, d)
  | check_prep_def modl (d as Typesyn _) =
      d
  | check_prep_def modl (d as Datatype _) =
      d
  | check_prep_def modl (Datatypecons dtco) =
      error "Attempted to add bare datatype constructor"
  | check_prep_def modl (d as Class _) =
      d
  | check_prep_def modl (Classmember _) =
      error "Attempted to add bare class member"
  | check_prep_def modl (d as Classinst ((class, (tyco, arity)), (_, memdefs))) =
      let
        val Class (_, (v, membrs)) = get_def modl class;
        val _ = if length memdefs > length memdefs
          then error "Too many member definitions given"
          else ();
        fun check_memdef (m, _) =
          if AList.defined (op =) memdefs m
          then () else error ("Missing definition for member " ^ quote m);
        val _ = map check_memdef memdefs;
      in d end
  | check_prep_def modl Classinstmember =
      error "Attempted to add bare class instance member";

fun postprocess_def (name, Datatype (_, constrs)) =
      (check_samemodule (name :: map fst constrs);
      fold (fn (co, _) =>
        add_def_incr true (co, Datatypecons name)
        #> add_dep (co, name)
        #> add_dep (name, co)
      ) constrs
      )
  | postprocess_def (name, Class (_, (_, membrs))) =
      (check_samemodule (name :: map fst membrs);
      fold (fn (m, _) =>
        add_def_incr true (m, Classmember name)
        #> add_dep (m, name)
        #> add_dep (name, m)
      ) membrs
      )
  | postprocess_def _ =
      I;


(* transaction protocol *)

fun ensure_def defgen strict msg name (dep, modl) =
  let
    (*FIXME represent dependencies as tuple (name, name -> string), for better error msgs*)
    val msg' = (case dep
     of NONE => msg
      | SOME dep => msg ^ ", required for " ^ quote dep)
      ^ (if strict then " (strict)" else " (non-strict)");
    fun add_dp NONE = I
      | add_dp (SOME dep) =
          debug_msg (fn _ => "adding dependency " ^ quote dep ^ " -> " ^ quote name)
          #> add_dep (dep, name);
    fun prep_def def modl =
      (check_prep_def modl def, modl);
    fun invoke_generator name defgen modl =
      if ! soft_exc (*that "!" isn't a "not"...*)
      then defgen name (SOME name, modl)
        handle FAIL (msgs, exc) =>
                if strict then raise FAIL (msg' :: msgs, exc)
                else (Bot, modl)
             | e => raise
                FAIL (["definition generator for " ^ quote name, msg'], SOME e)
      else defgen name (SOME name, modl)
        handle FAIL (msgs, exc) =>
              if strict then raise FAIL (msg' :: msgs, exc)
              else (Bot, modl);
  in
    modl
    |> (if can (get_def modl) name
        then
          debug_msg (fn _ => "asserting node " ^ quote name)
          #> add_dp dep
        else
          debug_msg (fn _ => "allocating node " ^ quote name ^ (if strict then " (strict)" else " (non-strict)"))
          #> ensure_bot name
          #> add_dp dep
          #> debug_msg (fn _ => "creating node " ^ quote name)
          #> invoke_generator name defgen
          #-> (fn def => prep_def def)
          #-> (fn def =>
             debug_msg (fn _ => "addition of " ^ name ^ " := " ^ (Pretty.output o pretty_def) def)
          #> debug_msg (fn _ => "adding")
          #> add_def_incr strict (name, def)
          #> debug_msg (fn _ => "postprocessing")
          #> postprocess_def (name, def)
          #> debug_msg (fn _ => "adding done")
       ))
    |> pair dep
  end;

fun succeed some (_, modl) = (some, modl);

fun fail msg (_, modl) = raise FAIL ([msg], NONE);

fun message msg f trns =
  f trns handle FAIL (msgs, exc) =>
    raise FAIL (msg :: msgs, exc);

fun start_transact init f modl =
  let
    fun handle_fail f x =
      (f x
      handle FAIL (msgs, NONE) =>
        (error o cat_lines) ("Code generation failed, while:" :: msgs))
      handle FAIL (msgs, SOME e) =>
        ((Output.error_msg o cat_lines) ("Code generation failed, while:" :: msgs); raise e);
  in
    modl
    |> (if is_some init then ensure_bot (the init) else I)
    |> pair init
    |> handle_fail f
    |-> (fn x => fn (_, modl) => (x, modl))
  end;

fun add_eval_def (shallow, e) modl =
  let
    val name = "VALUE";
    val sname = NameSpace.pack [shallow, name];
  in
    modl
    |> add_def (sname, Fun ([([], e)], ([("a", [])], ITyVar "a")))
    |> fold (curry add_dep sname) (add_deps_of_term e [])
    |> pair name
  end;


(** eliminating classes in definitions **)

fun elim_classes modl (eqs, (sortctxt, ty)) =
  let
    fun elim_expr _ = ();
  in (error ""; (eqs, ty)) end;

(** generic serialization **)

(* resolving *)

structure NameMangler = NameManglerFun (
  type ctxt = (string * string -> string) * (string -> string option);
  type src = string * string;
  val ord = prod_ord string_ord string_ord;
  fun mk (postprocess, validate) ((shallow, name), 0) =
        let
          val name' = postprocess (shallow, name);
        in case validate name'
         of NONE => name'
          | _ => mk (postprocess, validate) ((shallow, name), 1)
        end
    | mk (postprocess, validate) (("", name), i) =
        postprocess ("", name ^ replicate_string i "'")
        |> perhaps validate
    | mk (postprocess, validate) ((shallow, name), 1) =
        postprocess (shallow, shallow ^ "_" ^ name)
        |> perhaps validate
    | mk (postprocess, validate) ((shallow, name), i) =
        postprocess (shallow, name ^ replicate_string i "'")
        |> perhaps validate;
  fun is_valid _ _ = true;
  fun maybe_unique _ _ = NONE;
  fun re_mangle _ dst = error ("No such definition name: " ^ quote dst);
);

fun mk_deresolver module nsp_conn postprocess validate =
  let
    datatype tabnode = N of string * tabnode Symtab.table option;
    fun mk module manglers tab =
      let
        fun mk_name name =
          case NameSpace.unpack name
           of [n] => ("", n)
            | [s, n] => (s, n);
        fun in_conn (shallow, conn) =
          member (op = : string * string -> bool) conn shallow;
        fun add_name name =
          let
            val n as (shallow, _) = mk_name name;
          in
            AList.map_entry_yield in_conn shallow (
              NameMangler.declare (postprocess, validate) n
              #-> (fn n' => pair (name, n'))
            ) #> apfst the
          end;
        val (renamings, manglers') =
          fold_map add_name (Graph.keys module) manglers;
        fun extend_tab (n, n') =
          if (length o NameSpace.unpack) n = 1
          then
            Symtab.update_new
              (n, N (n', SOME (mk ((dest_modl o Graph.get_node module) n) manglers' Symtab.empty)))
          else
            Symtab.update_new (n, N (n', NONE));
      in fold extend_tab renamings tab end;
    fun get_path_name [] tab =
          ([], SOME tab)
      | get_path_name [p] tab =
          let
            val SOME (N (p', tab')) = Symtab.lookup tab p
          in ([p'], tab') end
      | get_path_name [p1, p2] tab =
          (case Symtab.lookup tab p1
           of SOME (N (p', SOME tab')) =>
                let
                  val (ps', tab'') = get_path_name [p2] tab'
                in (p' :: ps', tab'') end
            | NONE =>
                let
                  val SOME (N (p', NONE)) = Symtab.lookup tab (NameSpace.pack [p1, p2])
                in ([p'], NONE) end)
      | get_path_name (p::ps) tab =
          let
            val SOME (N (p', SOME tab')) = Symtab.lookup tab p
            val (ps', tab'') = get_path_name ps tab'
          in (p' :: ps', tab'') end;
    fun deresolv tab prefix name =
      let
        val (common, (_, rem)) = chop_prefix (op =) (prefix, NameSpace.unpack name);
        val (_, SOME tab') = get_path_name common tab;
        val (name', _) = get_path_name rem tab';
      in NameSpace.pack name' end handle BIND => (error ("Missing name: " ^ quote name ^ ", in " ^ quote (NameSpace.pack prefix)));
  in deresolv (mk module (AList.make (K NameMangler.empty) nsp_conn) Symtab.empty) end;


(* serialization *)

fun serialize seri_defs seri_module validate postprocess nsp_conn name_root module =
  let
    val imptab = allimports_of module;
    val resolver = mk_deresolver module nsp_conn postprocess validate;
    fun sresolver s = (resolver o NameSpace.unpack) s
    fun mk_name prfx name =
      let
        val name_qual = NameSpace.pack (prfx @ [name])
      in (name_qual, resolver prfx name_qual) end;
    fun is_bot (_, (Def Bot)) = true
      | is_bot _ = false;
    fun mk_contents prfx module =
      map_filter (seri prfx)
        ((map (AList.make (Graph.get_node module)) o rev o Graph.strong_conn) module)
    and seri prfx [(name, Module modl)] =
          seri_module (resolver []) (map (resolver []) ((the o Symtab.lookup imptab) (NameSpace.pack (prfx @ [name]))))
            (mk_name prfx name, mk_contents (prfx @ [name]) modl)
      | seri prfx ds =
          case filter_out is_bot ds
           of [] => NONE
            | ds' => seri_defs sresolver (NameSpace.pack prfx)
                (map (fn (name, Def def) => (fst (mk_name prfx name), def (*|> tap (Pretty.writeln o pretty_def)*))) ds')
  in
    seri_module (resolver []) (map (resolver []) ((the o Symtab.lookup imptab) ""))
      (("", name_root), (mk_contents [] module))
  end;

end; (* struct *)

structure BasicCodegenThingol: BASIC_CODEGEN_THINGOL = CodegenThingol;
