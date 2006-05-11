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
  datatype iclasslookup = Instance of string * iclasslookup list list
                        | Lookup of class list * (string * int);
  datatype itype =
      `%% of string * itype list
    | `-> of itype * itype
    | ITyVar of vname;
  datatype iexpr =
      IConst of string * (iclasslookup list list * itype)
    | IVar of vname
    | `$ of iexpr * iexpr
    | `|-> of (vname * itype) * iexpr
    | INum of IntInf.int (*positive!*) * unit
    | IChar of string (*length one!*) * iexpr
    | IAbs of ((iexpr * itype) * iexpr) * iexpr
        (* (((binding expression (ve), binding type (vty)),
                body expression (be)), native expression (e0)) *)
    | ICase of ((iexpr * itype) * (iexpr * iexpr) list) * iexpr;
        (* ((discrimendum expression (de), discrimendum type (dty)),
                [(selector expression (se), body expression (be))]),
                native expression (e0)) *)
end;

signature CODEGEN_THINGOL =
sig
  include BASIC_CODEGEN_THINGOL;
  val `--> : itype list * itype -> itype;
  val `$$ : iexpr * iexpr list -> iexpr;
  val `|--> : (vname * itype) list * iexpr -> iexpr;
  val pretty_itype: itype -> Pretty.T;
  val pretty_iexpr: iexpr -> Pretty.T;
  val unfoldl: ('a -> ('a * 'b) option) -> 'a -> 'a * 'b list;
  val unfoldr: ('a -> ('b * 'a) option) -> 'a -> 'b list * 'a;
  val unfold_fun: itype -> itype list * itype;
  val unfold_app: iexpr -> iexpr * iexpr list;
  val unfold_abs: iexpr -> (iexpr * itype) list * iexpr;
  val unfold_let: iexpr -> ((iexpr * itype) * iexpr) list * iexpr;
  val unfold_const_app: iexpr ->
    ((string * (iclasslookup list list * itype)) * iexpr list) option;
  val add_constnames: iexpr -> string list -> string list;
  val add_varnames: iexpr -> string list -> string list;
  val is_pat: iexpr -> bool;
  val map_pure: (iexpr -> 'a) -> iexpr -> 'a;
  val resolve_tycos: (string -> string) -> itype * iexpr list -> itype * iexpr list;
  val resolve_consts: (string -> string) -> iexpr -> iexpr;
  val eta_expand: (string * (iclasslookup list list * itype)) * iexpr list -> int -> iexpr;
  

  type funn = (iexpr list * iexpr) list * (sortcontext * itype);
  type datatyp = sortcontext * (string * itype list) list;
  datatype prim =
      Pretty of Pretty.T
    | Name;
  datatype def =
      Undef
    | Prim of (string * prim list) list
    | Fun of funn
    | Typesyn of (vname * sort) list * itype
    | Datatype of datatyp
    | Datatypecons of string
    | Class of class list * (vname * (string * (sortcontext * itype)) list)
    | Classmember of class
    | Classinst of ((class * (string * (vname * sort) list))
          * (class * (string * iclasslookup list list)) list)
        * (string * ((string * funn) * iclasslookup list list)) list
    | Classinstmember;
  type module;
  type transact;
  type 'dst transact_fin;
  val pretty_def: def -> Pretty.T;
  val pretty_module: module -> Pretty.T; 
  val pretty_deps: module -> Pretty.T;
  val empty_module: module;
  val get_def: module -> string -> def;
  val add_prim: string -> (string * prim list) -> module -> module;
  val ensure_prim: string -> string -> module -> module;
  val merge_module: module * module -> module;
  val diff_module: module * module -> (string * def) list;
  val project_module: string list -> module -> module;
  val purge_module: string list -> module -> module;
  val has_nsp: string -> string -> bool;
  val succeed: 'a -> transact -> 'a transact_fin;
  val fail: string -> transact -> 'a transact_fin;
  val ensure_def: (string * (string -> transact -> def transact_fin)) list -> string
    -> string -> transact -> transact;
  val start_transact: string option -> (transact -> 'a * transact) -> module -> 'a * module;

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
fun debug_msg f x = (if !debug then Output.debug (f x) else (); x);
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

fun map_yield f [] = ([], [])
  | map_yield f (x::xs) =
      let
        val (y, x') = f x
        val (ys, xs') = map_yield f xs
      in (y::ys, x'::xs') end;

fun get_prefix eq ([], ys) = ([], ([], ys))
  | get_prefix eq (xs, []) = ([], (xs, []))
  | get_prefix eq (xs as x::xs', ys as y::ys') =
      if eq (x, y) then
        let val (ps', xys'') = get_prefix eq (xs', ys')
        in (x::ps', xys'') end
      else ([], (xs, ys));


(** language core - types, pattern, expressions **)

(* language representation *)

type vname = string;

type sortcontext = ClassPackage.sortcontext;
datatype iclasslookup = Instance of string * iclasslookup list list
                      | Lookup of class list * (string * int);

datatype itype =
    `%% of string * itype list
  | `-> of itype * itype
  | ITyVar of vname;

datatype iexpr =
    IConst of string * (iclasslookup list list * itype)
  | IVar of vname
  | `$ of iexpr * iexpr
  | `|-> of (vname * itype) * iexpr
  | INum of IntInf.int (*positive!*) * unit
  | IChar of string (*length one!*) * iexpr
  | IAbs of ((iexpr * itype) * iexpr) * iexpr
  | ICase of ((iexpr * itype) * (iexpr * iexpr) list) * iexpr;
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

fun pretty_iexpr (IConst (c, _)) =
      Pretty.str c
  | pretty_iexpr (IVar v) =
      Pretty.str ("?" ^ v)
  | pretty_iexpr (e1 `$ e2) =
      (Pretty.enclose "(" ")" o Pretty.breaks)
        [pretty_iexpr e1, pretty_iexpr e2]
  | pretty_iexpr ((v, ty) `|-> e) =
      (Pretty.enclose "(" ")" o Pretty.breaks)
        [Pretty.str v, Pretty.str "::", pretty_itype ty, Pretty.str "|->", pretty_iexpr e]
  | pretty_iexpr (INum (n, _)) =
      (Pretty.str o IntInf.toString) n
  | pretty_iexpr (IChar (c, _)) =
      (Pretty.str o quote) c
  | pretty_iexpr (IAbs (((e1, _), e2), _)) =
      (Pretty.enclose "(" ")" o Pretty.breaks)
        [pretty_iexpr e1, Pretty.str "|->", pretty_iexpr e2]
  | pretty_iexpr (ICase (((e, _), cs), _)) =
      (Pretty.enclose "(" ")" o Pretty.breaks) [
        Pretty.str "case",
        pretty_iexpr e,
        Pretty.enclose "(" ")" (map (fn (p, e) =>
          (Pretty.block o Pretty.breaks) [
            pretty_iexpr p,
            Pretty.str "=>",
            pretty_iexpr e
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
  (fn (v, ty) `|-> e => SOME ((IVar v, ty), e)
    | IAbs (((e1, ty), e2), _) => SOME ((e1, ty), e2)
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

fun is_pat (e as IConst (_, ([], _))) = true
  | is_pat (e as IVar _) = true
  | is_pat (e as (e1 `$ e2)) =
      is_pat e1 andalso is_pat e2
  | is_pat (e as INum _) = true
  | is_pat (e as IChar _) = true
  | is_pat e = false;

fun map_pure f (e as IConst _) =
      f e
  | map_pure f (e as IVar _) =
      f e
  | map_pure f (e as _ `$ _) =
      f e
  | map_pure f (e as _ `|-> _) =
      f e
  | map_pure _ (INum _) =
      error ("sorry, no pure representation of numerals so far")
  | map_pure f (IChar (_, e0)) =
      f e0
  | map_pure f (IAbs (_, e0)) =
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
  | add_constnames (INum _) =
      I
  | add_constnames (IChar _) =
      I
  | add_constnames (IAbs (_, e)) =
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
  | add_varnames (INum _) =
      I
  | add_varnames (IChar _) =
      I
  | add_varnames (IAbs (((ve, _), be), _)) =
      add_varnames ve #> add_varnames be
  | add_varnames (ICase (((de, _), bses), _)) =
      add_varnames de #> fold (fn (be, se) => add_varnames be #> add_varnames se) bses;

fun invent seed used =
  let
    val x = Term.variant used seed
  in (x, x :: used) end;

fun eta_expand (c as (_, (_, ty)), es) k =
  let
    val j = length es;
    val l = k - j;
    val tys = (curry Library.take l o curry Library.drop j o fst o unfold_fun) ty;
    val vs = [] |> fold add_varnames es |> fold_map invent (replicate l "x") |> fst;
  in vs ~~ tys `|--> IConst c `$$ es @ map IVar vs end;



(** language module system - definitions, modules, transactions **)

(* type definitions *)

type funn = (iexpr list * iexpr) list * (sortcontext * itype);
type datatyp = sortcontext * (string * itype list) list;

datatype prim =
    Pretty of Pretty.T
  | Name;

datatype def =
    Undef
  | Prim of (string * prim list) list
  | Fun of funn
  | Typesyn of (vname * sort) list * itype
  | Datatype of datatyp
  | Datatypecons of string
  | Class of class list * (vname * (string * (sortcontext * itype)) list)
  | Classmember of class
  | Classinst of ((class * (string * (vname * sort) list))
        * (class * (string * iclasslookup list list)) list)
      * (string * ((string * funn) * iclasslookup list list)) list
  | Classinstmember;

datatype node = Def of def | Module of node Graph.T;
type module = node Graph.T;
type transact = Graph.key option * module;
datatype 'dst transact_res = Succeed of 'dst | Fail of string list * exn option;
type 'dst transact_fin = 'dst transact_res * module;
exception FAIL of string list * exn option;

val eq_def = (op =) : def * def -> bool;

(* simple diagnosis *)

fun pretty_def Undef =
      Pretty.str "<UNDEF>"
  | pretty_def (Prim prims) =
      Pretty.str ("<PRIM " ^ (commas o map fst) prims ^ ">")
  | pretty_def (Fun (eqs, (sortctxt, ty))) =
      Pretty.enum " |" "" "" (
        map (fn (ps, body) =>
          Pretty.block [
            Pretty.enum "," "[" "]" (map pretty_iexpr ps),
            Pretty.str " |->",
            Pretty.brk 1,
            pretty_iexpr body,
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
        Pretty.str ("class var " ^ v ^ "extending "),
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
  | pretty_def (Classinst (((clsname, (tyco, arity)), _), _)) =
      Pretty.block [
        Pretty.str "class instance (",
        Pretty.str clsname,
        Pretty.str ", (",
        Pretty.str tyco,
        Pretty.str ", ",
        Pretty.enum "," "[" "]" (map (Pretty.enum "," "{" "}" o
          map Pretty.str o snd) arity),
        Pretty.str "))"
      ]
  | pretty_def Classinstmember =
      Pretty.str "class instance member";

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
  handle Empty => error ("not a qualified name: " ^ quote name);

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

fun add_def (name, def) =
  let
    val (modl, base) = dest_name name;
    fun add [] =
          Graph.new_node (base, Def def)
      | add (m::ms) =
          Graph.default_node (m, Module empty_module)
          #> Graph.map_node m (Module o add ms o dest_modl)
  in add modl end;

fun add_dep (name1, name2) modl =
  if name1 = name2 then modl
  else
    let
      val m1 = dest_name name1 |> apsnd single |> (op @);
      val m2 = dest_name name2 |> apsnd single |> (op @);
      val (ms, (r1, r2)) = get_prefix (op =) (m1, m2);
      val (ms, (s1::r1, s2::r2)) = get_prefix (op =) (m1, m2);
      val add_edge =
        if null r1 andalso null r2
        then Graph.add_edge
        else fn edge => (Graph.add_edge_acyclic edge
          handle Graph.CYCLES _ => error ("adding dependency "
            ^ quote name1 ^ " -> " ^ quote name2 ^ " would result in module dependency cycle"))
      fun add [] node =
            node
            |> add_edge (s1, s2)
        | add (m::ms) node =
            node
            |> Graph.map_node m (Module o add ms o dest_modl);
    in add ms modl end;

fun map_def name f =
  let
    val (modl, base) = dest_name name;
    fun mapp [] =
          Graph.map_node base (Def o f o dest_def)
      | mapp (m::ms) =
          Graph.map_node m (Module o mapp ms o dest_modl)
  in mapp modl end;

fun map_defs f =
  let
    fun mapp (Def def) =
          (Def o f) def
      | mapp (Module modl) =
          (Module o Graph.map_nodes mapp) modl
  in dest_modl o mapp o Module end;

fun fold_defs f =
  let
    fun fol prfix (name, (Def def, _)) =
          f (NameSpace.pack (prfix @ [name]), def)
      | fol prfix (name, (Module modl, _)) =
          Graph.fold (fol (prfix @ [name])) modl
  in Graph.fold (fol []) end;

fun add_deps f modl =
  modl
  |> fold add_dep ([] |> fold_defs (append o f) modl);

fun add_def_incr (name, Undef) module =
      (case try (get_def module) name
       of NONE => (error "attempted to add Undef to module")
        | SOME Undef => (error "attempted to add Undef to module")
        | SOME def' => map_def name (K def') module)
  | add_def_incr (name, def) module =
      (case try (get_def module) name
       of NONE => add_def (name, def) module
        | SOME Undef => map_def name (K def) module
        | SOME def' => if eq_def (def, def')
            then module
            else error ("tried to overwrite definition " ^ name));

fun add_prim name (target, primdef as _::_) =
  let
    val (modl, base) = dest_name name;
    fun add [] module =
          (case try (Graph.get_node module) base
           of NONE =>
                module
                |> Graph.new_node (base, (Def o Prim) [(target, primdef)])
            | SOME (Def (Prim prim)) =>
                if AList.defined (op =) prim target
                then error ("already primitive definition (" ^ target
                  ^ ") present for " ^ name)
                else
                  module
                  |> Graph.map_node base ((K o Def o Prim) (AList.update (op =)
                       (target, primdef) prim))
            | _ => error ("already non-primitive definition present for " ^ name))
      | add (m::ms) module =
          module
          |> Graph.default_node (m, Module empty_module)
          |> Graph.map_node m (Module o add ms o dest_modl)
  in add modl end;

fun ensure_prim name target =
  let
    val (modl, base) = dest_name name;
    fun ensure [] module =
          (case try (Graph.get_node module) base
           of NONE =>
                module
                |> Graph.new_node (base, (Def o Prim) [(target, [])])
            | SOME (Def (Prim prim)) =>
                module
                |> Graph.map_node base ((K o Def o Prim) (AList.default (op =)
                     (target, []) prim))
            | _ => module)
      | ensure (m::ms) module =
          module
          |> Graph.default_node (m, Module empty_module)
          |> Graph.map_node m (Module o ensure ms o dest_modl)
  in ensure modl end;

fun merge_module modl12 =
  let
    fun join_module _ (Module m1, Module m2) =
          Module (merge_module (m1, m2))
      | join_module name (Def d1, Def d2) =
          if eq_def (d1, d2) then Def d1 else Def d1 (*raise Graph.DUP name*)
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

local 

fun project_trans f names modl =
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
      |> f (Graph.all_succs module (defs @ map fst modls))
      |> fold (fn (name, modls) => Graph.map_node name (select modls)) modls
      |> Module;
  in
    Module modl
    |> select (fold (mk_ipath o dest_name)
         (filter NameSpace.is_qualified names) (PN ([], [])))
    |> dest_modl
  end;

in

val project_module = project_trans Graph.subgraph;
val purge_module = project_trans Graph.del_nodes;

end; (*local*)

fun imports_of modl name =
  let
    (*fun submodules prfx modl =
      cons prfx
      #> Graph.fold
          (fn (m, (Module modl, _)) => submodules (prfx @ [m]) modl
            | (_, (Def _, _)) => I) modl;
    fun get_modl name =
      fold (fn n => fn modl => (dest_modl oo Graph.get_node) modl n) name modl*)
    fun imports prfx [] modl =
          []
      | imports prfx (m::ms) modl =
          map (cons m) (imports (prfx @ [m]) ms ((dest_modl oo Graph.get_node) modl m))
          @ map single (Graph.imm_succs modl m)
  in
    modl
    |> imports [] name 
    (*|> cons name
    |> map (fn name => submodules name (get_modl name) [])
    |> flat
    |> remove (op =) name*)
    |> map NameSpace.pack
  end;

fun check_samemodule names =
  fold (fn name =>
    let
      val modn = (fst o dest_name) name
    in
     fn NONE => SOME modn
      | SOME mod' => if modn = mod' then SOME modn
          else error "inconsistent name prefix for simultanous names"
    end
  ) names NONE;

fun check_funeqs eqs =
  (fold (fn (pats, _) =>
    let
      val l = length pats
    in
     fn NONE => SOME l
      | SOME l' => if l = l' then SOME l
          else error "function definition with different number of arguments"
    end
  ) eqs NONE; eqs);

fun check_prep_def modl Undef =
      Undef
  | check_prep_def modl (d as Prim _) =
      d
  | check_prep_def modl (Fun (eqs, d)) =
      Fun (check_funeqs eqs, d)
  | check_prep_def modl (d as Typesyn _) =
      d
  | check_prep_def modl (d as Datatype _) =
      d
  | check_prep_def modl (Datatypecons dtco) =
      error "attempted to add bare datatype constructor"
  | check_prep_def modl (d as Class _) =
      d
  | check_prep_def modl (Classmember _) =
      error "attempted to add bare class member"
  | check_prep_def modl (Classinst ((d as ((class, (tyco, arity)), _), memdefs))) =
      let
        val Class (_, (v, membrs)) = get_def modl class;
        val _ = if length memdefs > length memdefs
          then error "too many member definitions given"
          else ();
        fun instant (w, ty) v =
          if v = w then ty else ITyVar v;
        fun mk_memdef (m, (sortctxt, ty)) =
          case AList.lookup (op =) memdefs m
           of NONE => error ("missing definition for member " ^ quote m)
            | SOME ((m', (eqs, (sortctxt', ty'))), lss) =>
                let
                  val sortctxt'' = sortctxt |> fold (fn v_sort => AList.update (op =) v_sort) arity;
                  val ty'' = instant_itype (instant (v, tyco `%% map (ITyVar o fst) arity)) ty;
                in if eq_ityp ((sortctxt'', ty''), (sortctxt', ty'))
                then (m, ((m', (check_funeqs eqs, (sortctxt', ty'))), lss))
                else
                  error ("inconsistent type for member definition " ^ quote m ^ " [" ^ v ^ "]: "
                    ^ (Pretty.output o Pretty.block o Pretty.breaks) [
                      pretty_sortcontext sortctxt'',
                      Pretty.str "|=>",
                      pretty_itype ty''
                    ] ^ " vs. " ^ (Pretty.output o Pretty.block o Pretty.breaks) [
                      pretty_sortcontext sortctxt',
                      Pretty.str "|=>",
                      pretty_itype ty'
                    ]
                  )
                end
      in Classinst (d, map mk_memdef membrs) end
  | check_prep_def modl Classinstmember =
      error "attempted to add bare class instance member";

fun postprocess_def (name, Datatype (_, constrs)) =
      (check_samemodule (name :: map fst constrs);
      fold (fn (co, _) =>
        add_def_incr (co, Datatypecons name)
        #> add_dep (co, name)
        #> add_dep (name, co)
      ) constrs
      )
  | postprocess_def (name, Class (_, (_, membrs))) =
      (check_samemodule (name :: map fst membrs);
      fold (fn (m, _) =>
        add_def_incr (m, Classmember name)
        #> add_dep (m, name)
        #> add_dep (name, m)
      ) membrs
      )
  | postprocess_def (name, Classinst (_, memdefs)) =
      (check_samemodule (name :: map (fst o fst o snd) memdefs);
      fold (fn (_, ((m', _), _)) =>
        add_def_incr (m', Classinstmember)
      ) memdefs
      )
  | postprocess_def _ =
      I;

fun succeed some (_, modl) = (Succeed some, modl);
fun fail msg (_, modl) = (Fail ([msg], NONE), modl);

fun check_fail _ (Succeed dst, trns) = (dst, trns)
  | check_fail msg (Fail (msgs, e), _) = raise FAIL (msg::msgs, e);

fun select_generator _ src [] modl =
      (SOME src, modl) |> fail ("no code generator available")
  | select_generator mk_msg src gens modl =
      let
        fun handle_fail msgs f =
          let
            in
              if ! soft_exc
              then
                (SOME src, modl) |> f
                handle FAIL exc => (Fail exc, modl)
                     | e => (Fail (msgs, SOME e), modl)
              else
                (SOME src, modl) |> f
                handle FAIL exc => (Fail exc, modl)
            end;
        fun select msgs [(gname, gen)] =
              handle_fail (msgs @ [mk_msg gname]) (gen src)
          | select msgs ((gname, gen)::gens) =
              let
                val msgs' = msgs @ [mk_msg gname]
              in case handle_fail msgs' (gen src)
               of (Fail (_, NONE), _) =>
                   select msgs' gens
               | result => result
          end;
      in select [] gens end;

fun ensure_def defgens msg name (dep, modl) =
  let
    val msg' = case dep
     of NONE => msg
      | SOME dep => msg ^ ", with dependency " ^ quote dep;
    fun add_dp NONE = I
      | add_dp (SOME dep) =
          debug_msg (fn _ => "adding dependency " ^ quote dep ^ " -> " ^ quote name)
          #> add_dep (dep, name);
    fun prep_def def modl =
      (check_prep_def modl def, modl);
  in
    modl
    |> (if can (get_def modl) name
        then
          debug_msg (fn _ => "asserting node " ^ quote name)
          #> add_dp dep
        else
          debug_msg (fn _ => "allocating node " ^ quote name)
          #> add_def (name, Undef)
          #> add_dp dep
          #> debug_msg (fn _ => "creating node " ^ quote name)
          #> select_generator (fn gname => "trying code generator "
               ^ gname ^ " for definition of " ^ quote name) name defgens
          #> debug_msg (fn _ => "checking creation of node " ^ quote name)
          #> check_fail msg'
          #-> (fn def => prep_def def)
          #-> (fn def =>
             debug_msg (fn _ => "addition of " ^ name ^ " := " ^ (Pretty.output o pretty_def) def)
          #> debug_msg (fn _ => "adding")
          #> add_def_incr (name, def)
          #> debug_msg (fn _ => "postprocessing")
          #> postprocess_def (name, def)
          #> debug_msg (fn _ => "adding done")
       ))
    |> pair dep
  end;

fun start_transact init f modl =
  let
    fun handle_fail f x =
      (f x
      handle FAIL (msgs, NONE) =>
        (error o cat_lines) ("code generation failed, while:" :: msgs))
      handle FAIL (msgs, SOME e) =>
        ((Output.error_msg o cat_lines) ("code generation failed, while:" :: msgs); raise e);
  in
    (init, modl)
    |> handle_fail f
    |-> (fn x => fn (_, module) => (x, module))
  end;



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
  fun re_mangle _ dst = error ("no such definition name: " ^ quote dst);
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
        val (common, (_, rem)) = get_prefix (op =) (prefix, NameSpace.unpack name);
        val (_, SOME tab') = get_path_name common tab;
        val (name', _) = get_path_name rem tab';
      in NameSpace.pack name' end;
  in deresolv (mk module (AList.make (K NameMangler.empty) nsp_conn) Symtab.empty) end;


(* serialization *)

fun serialize seri_defs seri_module validate postprocess nsp_conn name_root module =
  let
    val resolver = mk_deresolver module nsp_conn postprocess validate;
    fun sresolver s = (resolver o NameSpace.unpack) s
    fun mk_name prfx name =
      let
        val name_qual = NameSpace.pack (prfx @ [name])
      in (name_qual, resolver prfx name_qual) end;
    fun mk_contents prfx module =
      map_filter (seri prfx)
        ((map (AList.make (Graph.get_node module)) o rev o Graph.strong_conn) module)
    and seri prfx ([(name, Module modl)]) =
          seri_module (resolver []) (map (resolver []) (imports_of module (prfx @ [name])))
            (mk_name prfx name, mk_contents (prfx @ [name]) modl)
      | seri prfx ds =
          seri_defs sresolver (NameSpace.pack prfx)
            (map (fn (name, Def def) => (fst (mk_name prfx name), def)) ds)
  in
    seri_module (resolver []) (imports_of module [])
      (*map (resolver []) (Graph.strong_conn module |> flat |> rev)*)
      (("", name_root), (mk_contents [] module))
  end;

end; (* struct *)

structure BasicCodegenThingol: BASIC_CODEGEN_THINGOL = CodegenThingol;
