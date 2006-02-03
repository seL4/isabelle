(*  Title:      Pure/Tools/codegen_thingol.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Intermediate language ("Thin-gol") for code extraction.
*)

signature CODEGEN_THINGOL =
sig
  type vname = string;
  datatype classlookup = Instance of string * classlookup list list
                       | Lookup of class list * (string * int);
  datatype itype =
      IType of string * itype list
    | IFun of itype * itype
    | IVarT of vname * sort;
  datatype iexpr =
      IConst of (string * itype) * classlookup list list
    | IVarE of vname * itype
    | IApp of iexpr * iexpr
    | IAbs of (vname * itype) * iexpr
    | ICase of iexpr * (iexpr * iexpr) list;
  val mk_funs: itype list * itype -> itype;
  val mk_apps: iexpr * iexpr list -> iexpr;
  val mk_abss: (vname * itype) list * iexpr -> iexpr;
  val pretty_itype: itype -> Pretty.T;
  val pretty_iexpr: iexpr -> Pretty.T;
  val unfoldl: ('a -> ('a * 'b) option) -> 'a -> 'a * 'b list;
  val unfoldr: ('a -> ('b * 'a) option) -> 'a -> 'b list * 'a;
  val unfold_fun: itype -> itype list * itype;
  val unfold_app: iexpr -> iexpr * iexpr list;
  val unfold_abs: iexpr -> (vname * itype) list * iexpr;
  val unfold_let: iexpr -> (iexpr * iexpr) list * iexpr;
  val unfold_const_app: iexpr ->
    (((string * itype) * classlookup list list) * iexpr list) option;
  val ensure_pat: iexpr -> iexpr;
  val itype_of_iexpr: iexpr -> itype;

  val `%% : string * itype list -> itype;
  val `-> : itype * itype -> itype;
  val `--> : itype list * itype -> itype;
  val `$ : iexpr * iexpr -> iexpr;
  val `$$ : iexpr * iexpr list -> iexpr;
  val `|-> : (vname * itype) * iexpr -> iexpr;
  val `|--> : (vname * itype) list * iexpr -> iexpr;

  type funn = (iexpr list * iexpr) list * (ClassPackage.sortcontext * itype);
  datatype prim =
      Pretty of Pretty.T
    | Name of string;
  datatype def =
      Undef
    | Prim of (string * Pretty.T option) list
    | Fun of funn
    | Typesyn of (vname * string list) list * itype
    | Datatype of ((vname * string list) list * (string * itype list) list)
        * string list
    | Datatypecons of string
    | Class of (class list * (vname * (string * (ClassPackage.sortcontext * itype)) list))
        * string list
    | Classmember of class
    | Classinst of ((class * (string * (vname * sort) list))
          * (class * classlookup list list) list)
        * (string * funn) list;
  type module;
  type transact;
  type 'dst transact_fin;
  type gen_defgen = string -> transact -> def transact_fin;
  val pretty_def: def -> Pretty.T;
  val pretty_module: module -> Pretty.T; 
  val pretty_deps: module -> Pretty.T;
  val empty_module: module;
  val add_prim: string -> string list -> (string * Pretty.T) -> module -> module;
  val ensure_prim: string -> string -> module -> module;
  val get_def: module -> string -> def;
  val merge_module: module * module -> module;
  val partof: string list -> module -> module;
  val has_nsp: string -> string -> bool;
  val succeed: 'a -> transact -> 'a transact_fin;
  val fail: string -> transact -> 'a transact_fin;
  val gen_ensure_def: (string * gen_defgen) list -> string
    -> string -> transact -> transact;
  val start_transact: (transact -> 'a * transact) -> module -> 'a * module;

  val eta_expand: (string -> int) -> module -> module;
  val eta_expand_poly: module -> module;
  val unclash_vars: module -> module;

  val debug_level: int ref;
  val debug: int -> ('a -> string) -> 'a -> 'a;
  val soft_exc: bool ref;

  val serialize:
    ((string -> string) -> (string * def) list -> 'a option)
    -> (string list -> (string * string) * 'a list -> 'a option)
    -> (string -> string option)
    -> string list list -> string -> module -> 'a option;
end;

structure CodegenThingol: CODEGEN_THINGOL =
struct

(** auxiliary **)

val debug_level = ref 0;
fun debug d f x = (if d <= !debug_level then Output.debug (f x) else (); x);
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

infix 8 `%%;
infixr 6 `->;
infixr 6 `-->;
infix 4 `$;
infix 4 `$$;
infixr 3 `|->;
infixr 3 `|-->;

type vname = string;

datatype classlookup = Instance of string * classlookup list list
                     | Lookup of class list * (string * int);

datatype itype =
    IType of string * itype list
  | IFun of itype * itype
  | IVarT of vname * sort;

datatype iexpr =
    IConst of (string * itype) * classlookup list list
  | IVarE of vname * itype
  | IApp of iexpr * iexpr
  | IAbs of (vname * itype) * iexpr
  | ICase of iexpr * (iexpr * iexpr) list;

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

val mk_funs = Library.foldr IFun;
val mk_apps = Library.foldl IApp;
val mk_abss = Library.foldr IAbs;

val op `%% = IType;
val op `-> = IFun;
val op `$ = IApp;
val op `|-> = IAbs;
val op `--> = mk_funs;
val op `$$ = mk_apps;
val op `|--> = mk_abss;

fun pretty_itype (IType (tyco, tys)) =
      Pretty.enum "" "(" ")" (Pretty.str tyco :: map pretty_itype tys)
  | pretty_itype (IFun (ty1, ty2)) =
      Pretty.enum "" "(" ")" [pretty_itype ty1, Pretty.str "->", pretty_itype ty2]
  | pretty_itype (IVarT (v, sort)) =
      Pretty.str (v ^ enclose "|" "|" (space_implode "|" sort));

fun pretty_iexpr (IConst ((c, ty), _)) =
      Pretty.block [Pretty.str (c ^ "::"), pretty_itype ty]
  | pretty_iexpr (IVarE (v, ty)) =
      Pretty.block [Pretty.str ("?" ^ v ^ "::"), pretty_itype ty]
  | pretty_iexpr (IApp (e1, e2)) =
      Pretty.enclose "(" ")" [pretty_iexpr e1, Pretty.brk 1, pretty_iexpr e2]
  | pretty_iexpr (IAbs ((v, ty), e)) =
      Pretty.enclose "(" ")" [Pretty.str ("?" ^ v ^ " |->"), Pretty.brk 1, pretty_iexpr e]
  | pretty_iexpr (ICase (e, cs)) =
      Pretty.enclose "(" ")" [
        Pretty.str "case ",
        pretty_iexpr e,
        Pretty.enclose "(" ")" (map (fn (p, e) =>
          Pretty.block [
            pretty_iexpr p,
            Pretty.str " => ",
            pretty_iexpr e
          ]
        ) cs)
      ];

val unfold_fun = unfoldr
  (fn IFun t => SOME t
    | _ => NONE);

val unfold_app = unfoldl
  (fn IApp e => SOME e
    | _ => NONE);

val unfold_abs = unfoldr
  (fn IAbs b => SOME b
    | _ => NONE)

val unfold_let = unfoldr
  (fn ICase (e, [(p, e')]) => SOME ((p, e), e')
    | _ => NONE);

fun unfold_const_app e = 
 case unfold_app e
  of (IConst x, es) => SOME (x, es)
   | _ => NONE;

fun map_itype f_itype (IType (tyco, tys)) =
      tyco `%% map f_itype tys
  | map_itype f_itype (IFun (t1, t2)) =
      f_itype t1 `-> f_itype t2
  | map_itype _ (ty as IVarT _) =
      ty;

fun map_iexpr f (IApp (e1, e2)) =
      f e1 `$ f e2
  | map_iexpr f (IAbs (v, e)) =
      v `|-> f e
  | map_iexpr f (ICase (e, ps)) =
      ICase (f e, map (fn (p, e) => (f p, f e)) ps)
  | map_iexpr _ (e as IConst _) =
      e
  | map_iexpr _ (e as IVarE _) =
      e;

fun map_atype f (ty as IVarT _) =
      f ty
  | map_atype f ty =
      map_itype (map_atype f) ty;

fun map_aexpr f (e as IConst _) = 
      f e
  | map_aexpr f (e as IVarE _) =
      f e
  | map_aexpr f e =
      map_iexpr (map_aexpr f) e;

fun map_iexpr_itype f =
  let
    fun mapp (IConst ((c, ty), ctxt)) = IConst ((c, f ty), ctxt)
      | mapp (IVarE (v, ty)) = IVarE (v, f ty)
  in map_aexpr mapp end;

fun fold_atype f (IFun (ty1, ty2)) =
      fold_atype f ty1 #> fold_atype f ty2
  | fold_atype f (ty as IType _) =
      f ty
  | fold_atype f (ty as IVarT _) =
      f ty;

fun fold_aexpr f (IApp (e1, e2)) =
      fold_aexpr f e1 #> fold_aexpr f e2
  | fold_aexpr f (IAbs (v, e)) =
      fold_aexpr f e
  | fold_aexpr f (ICase (e, ps)) =
      fold_aexpr f e #> fold (fn (p, e) => fold_aexpr f p #> fold_aexpr f e) ps
  | fold_aexpr f (e as IConst _) =
      f e
  | fold_aexpr f (e as IVarE _) =
      f e;

fun eq_itype (ty1, ty2) =
  let
    exception NO_MATCH;
    fun eq (IVarT (v1, sort1)) (IVarT (v2, sort2)) subs =
          if sort1 <> sort2
          then raise NO_MATCH
          else
            (case AList.lookup (op =) subs v1
             of NONE => subs |> AList.update (op =) (v1, v2)
              | (SOME v1') =>
                  if v1' <> v2
                  then raise NO_MATCH
                  else subs)
      | eq (IType (tyco1, tys1)) (IType (tyco2, tys2)) subs =
          if tyco1 <> tyco2
          then raise NO_MATCH
          else subs |> fold2 eq tys1 tys2
      | eq (IFun (ty11, ty12)) (IFun (ty21, ty22)) subs =
          subs |> eq ty11 ty21 |> eq ty12 ty22
      | eq _ _ _ = raise NO_MATCH;
  in
    (eq ty1 ty2 []; true)
    handle NO_MATCH => false
  end;

fun instant_itype f =
  let
    fun instant (IVarT x) = f x
      | instant y = map_itype instant y;
  in map_itype instant end;


(* simple diagnosis *)

fun pretty_itype (IType (tyco, tys)) =
      Pretty.enum "" "(" ")" (Pretty.str tyco :: map pretty_itype tys)
  | pretty_itype (IFun (ty1, ty2)) =
      Pretty.enum "" "(" ")" [pretty_itype ty1, Pretty.str "->", pretty_itype ty2]
  | pretty_itype (IVarT (v, sort)) =
      Pretty.str (v ^ enclose "|" "|" (space_implode "|" sort));

fun pretty_iexpr (IConst ((c, ty), _)) =
      Pretty.block [Pretty.str (c ^ "::"), pretty_itype ty]
  | pretty_iexpr (IVarE (v, ty)) =
      Pretty.block [Pretty.str ("?" ^ v ^ "::"), pretty_itype ty]
  | pretty_iexpr (IApp (e1, e2)) =
      Pretty.enclose "(" ")" [pretty_iexpr e1, Pretty.brk 1, pretty_iexpr e2]
  | pretty_iexpr (IAbs ((v, ty), e)) =
      Pretty.enclose "(" ")" [Pretty.str ("?" ^ v ^ " |->"), Pretty.brk 1, pretty_iexpr e]
  | pretty_iexpr (ICase (e, cs)) =
      Pretty.enclose "(" ")" [
        Pretty.str "case ",
        pretty_iexpr e,
        Pretty.enclose "(" ")" (map (fn (p, e) =>
          Pretty.block [
            pretty_iexpr p,
            Pretty.str " => ",
            pretty_iexpr e
          ]
        ) cs)
      ];


(* language auxiliary *)

fun itype_of_iexpr (IConst ((_, ty), s)) = ty
  | itype_of_iexpr (IVarE (_, ty)) = ty
  | itype_of_iexpr (e as IApp (e1, e2)) = (case itype_of_iexpr e1
      of (IFun (ty2, ty')) =>
            if ty2 = itype_of_iexpr e2
            then ty'
            else error ("inconsistent application: in " ^ Pretty.output (pretty_iexpr e)
              ^ ", " ^ (Pretty.output o pretty_itype) ty2
              ^ " vs. " ^ (Pretty.output o pretty_itype o itype_of_iexpr) e2)
       | _ => error ("expression is not a function: " ^ Pretty.output (pretty_iexpr e1)))
  | itype_of_iexpr (IAbs ((_, ty1), e2)) = ty1 `-> itype_of_iexpr e2
  | itype_of_iexpr (ICase ((_, [(_, e)]))) = itype_of_iexpr e;

fun ensure_pat (e as IConst (_, [])) = e
  | ensure_pat (e as IVarE _) = e
  | ensure_pat (e as IApp (e1, e2)) =
      (ensure_pat e1 `$ ensure_pat e2; e)
  | ensure_pat e =
      error ("illegal expression for pattern: " ^ (Pretty.output o pretty_iexpr) e);

fun type_vnames ty = 
  let
    fun extr (IVarT (v, _)) =
      insert (op =) v
  in fold_atype extr ty end;

fun expr_names e =
  let
    fun extr (IConst ((c, _), _)) =
          insert (op =) c
      | extr (IVarE (v, _)) =
          insert (op =) v
  in fold_aexpr extr e end;

fun invent seed used =
  let
    val x = Term.variant used seed
  in (x, x :: used) end;



(** language module system - definitions, modules, transactions **)

(* type definitions *)

type funn = (iexpr list * iexpr) list * (ClassPackage.sortcontext * itype);

datatype prim =
    Pretty of Pretty.T
  | Name of string;

datatype def =
    Undef
  | Prim of (string * Pretty.T option) list
  | Fun of funn
  | Typesyn of (vname * string list) list * itype
  | Datatype of ((vname * string list) list * (string * itype list) list)
      * string list
  | Datatypecons of string
  | Class of (class list * (vname * (string * (ClassPackage.sortcontext * itype)) list))
      * string list
  | Classmember of class
  | Classinst of ((class * (string * (vname * sort) list))
        * (class * classlookup list list) list)
      * (string * funn) list;

datatype node = Def of def | Module of node Graph.T;
type module = node Graph.T;
type transact = Graph.key option * module;
datatype 'dst transact_res = Succeed of 'dst | Fail of string list * exn option;
type 'dst transact_fin = 'dst transact_res * module;
type gen_defgen = string -> transact -> def transact_fin;
exception FAIL of string list * exn option;

val eq_def = (op =);

(* simple diagnosis *)

fun pretty_def Undef =
      Pretty.str "<UNDEF>"
  | pretty_def (Prim prims) =
      Pretty.str ("<PRIM " ^ (commas o map fst) prims ^ ">")
  | pretty_def (Fun (eqs, (_, ty))) =
      Pretty.enum " |" "" "" (
        map (fn (ps, body) =>
          Pretty.block [
            Pretty.enum "," "[" "]" (map pretty_iexpr ps),
            Pretty.str " |->",
            Pretty.brk 1,
            pretty_iexpr body,
            Pretty.str "::",
            pretty_itype ty
          ]) eqs
        )
  | pretty_def (Typesyn (vs, ty)) =
      Pretty.block [
        Pretty.list "(" ")" (map (pretty_itype o IVarT) vs),
        Pretty.str " |=> ",
        pretty_itype ty
      ]
  | pretty_def (Datatype ((vs, cs), insts)) =
      Pretty.block [
        Pretty.list "(" ")" (map (pretty_itype o IVarT) vs),
        Pretty.str " |=> ",
        Pretty.enum " |" "" ""
          (map (fn (c, tys) => (Pretty.block o Pretty.breaks)
            (Pretty.str c :: map pretty_itype tys)) cs),
        Pretty.str ", instances ",
        Pretty.enum "," "[" "]" (map Pretty.str insts)
      ]
  | pretty_def (Datatypecons dtname) =
      Pretty.str ("cons " ^ dtname)
  | pretty_def (Class ((supcls, (v, mems)), insts)) =
      Pretty.block [
        Pretty.str ("class var " ^ v ^ "extending "),
        Pretty.enum "," "[" "]" (map Pretty.str supcls),
        Pretty.str " with ",
        Pretty.enum "," "[" "]"
          (map (fn (m, (_, ty)) => Pretty.block
            [Pretty.str (m ^ "::"), pretty_itype ty]) mems),
        Pretty.str " instances ",
        Pretty.enum "," "[" "]" (map Pretty.str insts)
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
      ];

fun pretty_module modl =
  let
    fun pretty (name, Module modl) =
          Pretty.block (
            Pretty.str ("module " ^ name ^ " {")
            :: Pretty.brk 1
            :: Pretty.chunks (map pretty (AList.make (Graph.get_node modl)
                 (Graph.strong_conn modl |> List.concat |> rev)))
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
        val preds = fold (remove (op =)) mutbs preds_;
        val succs = fold (remove (op =)) mutbs succs_;
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
    |> List.concat
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
        else Graph.add_edge_acyclic
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
    fun fol prfix (name, Def def) =
          f (NameSpace.pack (prfix @ [name]), def)
      | fol prfix (name, Module modl) =
          Graph.fold_nodes (fol (prfix @ [name])) modl
  in Graph.fold_nodes (fol []) end;

fun add_deps f modl =
  modl
  |> fold add_dep ([] |> fold_defs (append o f) modl);

fun ensure_def (name, Undef) module =
      (case try (get_def module) name
       of NONE => (error "attempted to add Undef to module")
        | SOME Undef => (error "attempted to add Undef to module")
        | SOME def' => map_def name (K def') module)
  | ensure_def (name, def) module =
      (case try (get_def module) name
       of NONE => add_def (name, def) module
        | SOME Undef => map_def name (K def) module
        | SOME def' => if eq_def (def, def')
            then module
            else error ("tried to overwrite definition " ^ name));

fun add_prim name deps (target, primdef) =
  let
    val (modl, base) = dest_name name;
    fun add [] module =
          (case try (Graph.get_node module) base
           of NONE =>
                module
                |> Graph.new_node (base, (Def o Prim) [(target, SOME primdef)])
            | SOME (Def (Prim prim)) =>
                if AList.defined (op =) prim target
                then error ("already primitive definition (" ^ target
                  ^ ") present for " ^ name)
                else
                  module
                  |> Graph.map_node base ((K o Def o Prim) (AList.update (op =)
                       (target, SOME primdef) prim))
            | _ => error ("already non-primitive definition present for " ^ name))
      | add (m::ms) module =
          module
          |> Graph.default_node (m, Module empty_module)
          |> Graph.map_node m (Module o add ms o dest_modl)
  in
    add modl
    #> fold (curry add_dep name) deps
  end;

fun ensure_prim name target =
  let
    val (modl, base) = dest_name name;
    fun ensure [] module =
          (case try (Graph.get_node module) base
           of NONE =>
                module
                |> Graph.new_node (base, (Def o Prim) [(target, NONE)])
            | SOME (Def (Prim prim)) =>
                module
                |> Graph.map_node base ((K o Def o Prim) (AList.default (op =)
                     (target, NONE) prim))
            | _ => module)
      | ensure (m::ms) module =
          module
          |> Graph.default_node (m, Module empty_module)
          |> Graph.map_node m (Module o ensure ms o dest_modl)
  in ensure modl end;

fun merge_module modl12 =
  let
    fun join_module (Module m1, Module m2) =
          (SOME o Module) (merge_module (m1, m2))
      | join_module (Def d1, Def d2) =
          if eq_def (d1, d2) then (SOME o Def) d1 else NONE
      | join_module _ =
          NONE
  in Graph.join (K join_module) modl12 end;

fun partof names modl =
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
      |> Graph.subgraph (Graph.all_succs module (defs @ map fst modls))
      |> fold (fn (name, modls) => Graph.map_node name (select modls)) modls
      |> Module;
  in
    Module modl
    |> select (fold (mk_ipath o dest_name)
         (filter NameSpace.is_qualified names) (PN ([], [])))
    |> dest_modl
  end;

fun imports_of modl name =
  let
    fun imports prfx [] modl =
          []
      | imports prfx (m::ms) modl =
          map (cons m) (imports (prfx @ [m]) ms ((dest_modl oo Graph.get_node) modl m))
          @ map single (Graph.imm_succs modl m);
  in
    modl
    |> imports [] name 
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
  | check_prep_def modl (d as Datatype (_, insts)) =
      if null insts
      then d
      else error "attempted to add datatype with bare instances"
  | check_prep_def modl (Datatypecons dtco) =
      error "attempted to add bare datatype constructor"
  | check_prep_def modl (d as Class ((_, (v, membrs)), insts)) =
      if null insts
      then
        if member (op =) (map fst (Library.flat (map (fst o snd) membrs))) v
        then error "incorrectly abstracted class type variable"
        else d
      else error "attempted to add class with bare instances"
  | check_prep_def modl (Classmember _) =
      error "attempted to add bare class member"
  | check_prep_def modl (Classinst ((d as ((class, (tyco, arity)), _), memdefs))) =
      let
        val Class ((_, (v, membrs)), _) = get_def modl class;
        val _ = if length memdefs > length memdefs
          then error "too many member definitions given"
          else ();
        fun instant (w, ty) (var as (v, _)) =
          if v = w then ty else IVarT var;
        fun mk_memdef (m, (ctxt, ty)) =
          case AList.lookup (op =) memdefs m
           of NONE => error ("missing definition for member " ^ quote m)
            | SOME (eqs, (ctxt', ty')) =>
                if eq_itype (instant_itype (instant (v, tyco `%% map IVarT arity)) ty, ty')
                then (m, (check_funeqs eqs, (ctxt', ty')))
                else error ("inconsistent type for member definition " ^ quote m)
      in Classinst (d, map mk_memdef membrs) end;

fun postprocess_def (name, Datatype ((_, constrs), _)) =
      (check_samemodule (name :: map fst constrs);
      fold (fn (co, _) =>
        ensure_def (co, Datatypecons name)
        #> add_dep (co, name)
        #> add_dep (name, co)
      ) constrs
      )
  | postprocess_def (name, Class ((_, (_, membrs)), _)) =
      (check_samemodule (name :: map fst membrs);
      fold (fn (m, _) =>
        ensure_def (m, Classmember name)
        #> add_dep (m, name)
        #> add_dep (name, m)
      ) membrs
      )
  | postprocess_def (name, Classinst (((class, (tyco, _)), _), _)) =
      map_def class (fn Datatype (d, insts) => Datatype (d, name::insts)
                      | d => d)
      #> map_def class (fn Class (d, insts) => Class (d, name::insts))
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

fun gen_ensure_def defgens msg name (dep, modl) =
  let
    val msg' = case dep
     of NONE => msg
      | SOME dep => msg ^ ", with dependency " ^ quote dep;
    fun add_dp NONE = I
      | add_dp (SOME dep) =
          debug 9 (fn _ => "adding dependency " ^ quote dep ^ " -> " ^ quote name)
          #> add_dep (dep, name);
    fun prep_def def modl =
      (check_prep_def modl def, modl);
  in
    modl
    |> (if can (get_def modl) name
        then
          debug 9 (fn _ => "asserting node " ^ quote name)
          #> add_dp dep
        else
          debug 9 (fn _ => "allocating node " ^ quote name)
          #> add_def (name, Undef)
          #> add_dp dep
          #> debug 9 (fn _ => "creating node " ^ quote name)
          #> select_generator (fn gname => "trying code generator "
               ^ gname ^ " for definition of " ^ quote name) name defgens
          #> debug 9 (fn _ => "checking creation of node " ^ quote name)
          #> check_fail msg'
          #-> (fn def => prep_def def)
          #-> (fn def =>
             debug 10 (fn _ => "addition of " ^ name
               ^ " := " ^ (Pretty.output o pretty_def) def)
          #> debug 10 (fn _ => "adding")
          #> ensure_def (name, def)
          #> debug 10 (fn _ => "postprocessing")
          #> postprocess_def (name, def)
          #> debug 10 (fn _ => "adding done")
       ))
    |> pair dep
  end;

fun start_transact f modl =
  let
    fun handle_fail f modl =
      (((NONE, modl) |> f)
      handle FAIL (msgs, NONE) =>
        (error o cat_lines) ("code generation failed, while:" :: msgs))
      handle FAIL (msgs, SOME e) =>
        ((writeln o cat_lines) ("code generation failed, while:" :: msgs); raise e);
  in
    modl
    |> handle_fail f
    |-> (fn x => fn (_, module) => (x, module))
  end;



(** generic transformation **)

fun map_def_fun f (Fun funn) =
      Fun (f funn)
  | map_def_fun _ def = def;

fun map_def_fun_expr f (eqs, cty) =
  (map (fn (ps, rhs) => (map f ps, f rhs)) eqs, cty);

fun eta_expand query =
  let
    fun eta e =
     case unfold_const_app e
      of SOME (((f, ty), ls), es) =>
          let
            val delta = query f - length es;
            val add_n = if delta < 0 then 0 else delta;
            val tys =
              (fst o unfold_fun) ty
              |> curry Library.drop (length es)
              |> curry Library.take add_n
            val add_vars =
              Term.invent_names (fold expr_names es []) "x" add_n ~~ tys;
          in
            add_vars `|--> IConst ((f, ty), ls) `$$ es `$$ map IVarE add_vars
          end
       | NONE => map_iexpr eta e;
  in (map_defs o map_def_fun o map_def_fun_expr) eta end;

val eta_expand_poly =
  let
    fun eta (funn as ([([], e)], cty as (sortctxt, (ty as IFun (ty1, ty2))))) =
          if (not o null) sortctxt
            orelse null (type_vnames ty [])
          then funn
          else
            let
              val add_var = (hd (Term.invent_names (expr_names e []) "x" 1), ty1)
            in (([([IVarE add_var], add_var `|-> e)], cty)) end
      | eta funn = funn;
  in (map_defs o map_def_fun) eta end;

val unclash_vars = 
  let
    fun unclash (eqs, (sortctxt, ty)) =
      let
        val used_expr =
          fold (fn (pats, rhs) => fold expr_names pats #> expr_names rhs) eqs [];
        val used_type = map fst sortctxt;
        val clash = gen_union (op =) (used_expr, used_type);
        val rename_map = fold_map (fn c => invent c #-> (fn c' => pair (c, c'))) clash [] |> fst;
        fun rename (v, sort) =
          (perhaps (AList.lookup (op =) rename_map) v, sort);
        val rename_typ = instant_itype (IVarT o rename);
        val rename_expr = map_iexpr_itype rename_typ;
        fun rename_eq (args, rhs) = (map rename_expr args, rename_expr rhs)
      in
        (map rename_eq eqs, (map rename sortctxt, rename_typ ty))
      end;
  in (map_defs o map_def_fun) unclash end;



(** generic serialization **)

(* resolving *)

structure NameMangler = NameManglerFun (
  type ctxt = (string * string -> string) * (string -> string option);
  type src = string * string;
  val ord = prod_ord string_ord string_ord;
  fun mk (preprocess, validate) ((shallow, name), 0) =
        (case validate (preprocess (shallow, name))
         of NONE => name
          | _ => mk (preprocess, validate) ((shallow, name), 1))
    | mk (preprocess, validate) (("", name), i) =
        preprocess ("", name ^ "_" ^ string_of_int (i+1))
        |> perhaps validate
    | mk (preprocess, validate) ((shallow, name), i) =
        preprocess (shallow, shallow ^ "_" ^ name ^ "_" ^ string_of_int (i+1))
        |> perhaps validate;
  fun is_valid _ _ = true;
  fun maybe_unique _ _ = NONE;
  fun re_mangle _ dst = error ("no such definition name: " ^ quote dst);
);

fun mk_deresolver module nsp_conn preprocess validate =
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
            fun diag (nm as (name, n')) = (writeln ("resolving " ^ quote name ^ " to " ^ quote n'); nm);
          in
            AList.map_entry_yield in_conn shallow (
              NameMangler.declare (preprocess, validate) n
              #-> (fn n' => pair (name, n'))
            ) #> apfst the #> apfst diag
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
          case Symtab.lookup tab p1
           of SOME (N (p', SOME tab')) => 
                let
                  val (ps', tab'') = get_path_name [p2] tab'
                in (p' :: ps', tab'') end
            | NONE =>
                let
                  val SOME (N (p', NONE)) = Symtab.lookup tab (NameSpace.pack [p1, p2])
                in ([p'], NONE) end
      | get_path_name (p::ps) tab =
          let
            val SOME (N (p', SOME tab')) = Symtab.lookup tab p
            val (ps', tab'') = get_path_name ps tab'
          in (p' :: ps', tab'') end;
    fun deresolv tab prefix name =
      if (is_some o Int.fromString) name
      then name
      else let
        val (common, (_, rem)) = get_prefix (op =) (prefix, NameSpace.unpack name);
        val (_, SOME tab') = get_path_name common tab;
        val (name', _) = get_path_name rem tab';
      in NameSpace.pack name' end;
  in deresolv (mk module (AList.make (K NameMangler.empty) nsp_conn) Symtab.empty) end;


(* serialization *)

fun serialize seri_defs seri_module validate nsp_conn name_root module =
  let
    val resolver = mk_deresolver module nsp_conn snd validate;
    fun mk_name prfx name =
      let
        val name_qual = NameSpace.pack (prfx @ [name])
      in (name_qual, resolver prfx name_qual) end;
    fun mk_contents prfx module =
      List.mapPartial (seri prfx)
        ((map (AList.make (Graph.get_node module)) o rev o Graph.strong_conn) module)
    and seri prfx ([(name, Module modl)]) =
          seri_module (map (resolver []) (imports_of module (prfx @ [name])))
            (mk_name prfx name, mk_contents (prfx @ [name]) modl)
      | seri prfx ds =
          seri_defs (resolver prfx)
            (map (fn (name, Def def) => (fst (mk_name prfx name), def)) ds)
  in
    seri_module (map (resolver []) (Graph.strong_conn module |> List.concat |> rev))
      (("", name_root), (mk_contents [] module))
  end;

end; (* struct *)
