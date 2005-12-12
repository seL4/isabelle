(*  Title:      Pure/Tools/codegen_thingol.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Intermediate language ("Thin-gol") for code extraction.
*)

signature CODEGEN_THINGOL =
sig
  type vname = string;
  datatype itype =
      IType of string * itype list
    | IFun of itype * itype
    | IVarT of vname * sort
    | IDictT of (string * itype) list;
  datatype ipat =
      ICons of (string * ipat list) * itype
    | IVarP of vname * itype;
  datatype iexpr =
      IConst of string * itype
    | IVarE of vname * itype
    | IApp of iexpr * iexpr
    | IInst of iexpr * ClassPackage.sortlookup list list
    | IAbs of (vname * itype) * iexpr
    | ICase of iexpr * (ipat * iexpr) list
    | IDictE of (string * iexpr) list
    | ILookup of (string list * vname);
  val mk_funs: itype list * itype -> itype;
  val mk_apps: iexpr * iexpr list -> iexpr;
  val mk_abss: (vname * itype) list * iexpr -> iexpr;
  val pretty_itype: itype -> Pretty.T;
  val pretty_ipat: ipat -> Pretty.T;
  val pretty_iexpr: iexpr -> Pretty.T;
  val unfoldl: ('a -> ('a * 'b) option) -> 'a -> 'a * 'b list;
  val unfoldr: ('a -> ('b * 'a) option) -> 'a -> 'b list * 'a;
  val unfold_fun: itype -> itype list * itype;
  val unfold_app: iexpr -> iexpr * iexpr list;
  val unfold_abs: iexpr -> (vname * itype) list * iexpr;
  val unfold_let: iexpr -> (ipat * iexpr) list * iexpr;
  val itype_of_iexpr: iexpr -> itype;
  val itype_of_ipat: ipat -> itype;
  val ipat_of_iexpr: iexpr -> ipat;
  val eq_itype: itype * itype -> bool;
  val tvars_of_itypes: itype list -> string list;
  val vars_of_ipats: ipat list -> string list;
  val vars_of_iexprs: iexpr list -> string list;

  datatype def =
      Nop
    | Fun of (ipat list * iexpr) list * (ClassPackage.sortcontext * itype)
    | Typesyn of (vname * string list) list * itype
    | Datatype of (vname * string list) list * (string * itype list) list * string list
    | Datatypecons of string
    | Class of class list * vname * (string * (ClassPackage.sortcontext * itype)) list * string list
    | Classmember of class
    | Classinst of class * (string * (vname * string list) list) * (string * string) list;
  type module;
  type transact;
  type 'dst transact_fin;
  type ('src, 'dst) gen_exprgen = 'src -> transact -> 'dst transact_fin;
  type gen_defgen = string -> transact -> (def * string list) transact_fin;
  val pretty_def: def -> Pretty.T;
  val pretty_module: module -> Pretty.T; 
  val pretty_deps: module -> Pretty.T;
  val empty_module: module;
  val get_def: module -> string -> def;
  val merge_module: module * module -> module;
  val partof: string list -> module -> module;
  val succeed: 'a -> transact -> 'a transact_fin;
  val fail: string -> transact -> 'a transact_fin;
  val gen_invoke: (string * ('src, 'dst) gen_exprgen) list -> string
    -> 'src -> transact -> 'dst * transact;
  val gen_ensure_def: (string * gen_defgen) list -> string
    -> string -> transact -> transact;
  val start_transact: (transact -> 'a * transact) -> module -> 'a * module;

  val class_eq: string;
  val type_bool: string;
  val type_pair: string;
  val type_list: string;
  val type_integer: string;
  val cons_pair: string;
  val fun_eq: string;
  val fun_fst: string;
  val fun_snd: string;
  val Type_integer: itype;
  val Cons_true: iexpr;
  val Cons_false: iexpr;
  val Cons_pair: iexpr;
  val Cons_nil: iexpr;
  val Cons_cons: iexpr;
  val Fun_eq: iexpr;
  val Fun_not: iexpr;
  val Fun_and: iexpr;
  val Fun_or: iexpr;
  val Fun_if: iexpr;
  val Fun_fst: iexpr;
  val Fun_snd: iexpr;
  val Fun_0: iexpr;
  val Fun_1: iexpr;
  val Fun_add: iexpr;
  val Fun_mult: iexpr;
  val Fun_minus: iexpr;
  val Fun_lt: iexpr;
  val Fun_le: iexpr;
  val Fun_wfrec: iexpr;

  val prims: string list;
  val invoke_eq: ('a -> transact -> itype * transact)
    -> (string * (def * (string * sort) list) -> transact -> transact)
    -> 'a -> transact -> bool * transact;
  val extract_defs: iexpr -> string list;
  val eta_expand: (string -> int) -> module -> module;
  val eta_expand_poly: module -> module;
  val tupelize_cons: module -> module;
  val eliminate_classes: module -> module;

  val debug_level : int ref;
  val debug : int -> ('a -> string) -> 'a -> 'a;
  val soft_exc: bool ref;

  val serialize:
    ((string -> string) -> (string * def) list -> Pretty.T option)
    -> (string * Pretty.T list -> Pretty.T)
    -> (string -> string option)
    -> string list list -> string -> module -> Pretty.T
end;

signature CODEGEN_THINGOL_OP =
sig
  include CODEGEN_THINGOL;
  val `%% : string * itype list -> itype;
  val `-> : itype * itype -> itype;
  val `--> : itype list * itype -> itype;
  val `$ : iexpr * iexpr -> iexpr;
  val `$$ : iexpr * iexpr list -> iexpr;
  val `|-> : (vname * itype) * iexpr -> iexpr;
  val `|--> : (vname * itype) list * iexpr -> iexpr;
end;


structure CodegenThingolOp: CODEGEN_THINGOL_OP =
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

fun get_prefix eq ([], ys) = ([], [], ys)
  | get_prefix eq (xs, []) = ([], xs, [])
  | get_prefix eq (xs as x::xs', ys as y::ys') =
      if eq (x, y) then
        let val (ps', xs'', ys'') = get_prefix eq (xs', ys')
        in (x::ps', xs'', ys'') end
      else ([], xs, ys);


(** language core - types, pattern, expressions **)

(* language representation *)

infix 8 `%%;
infixr 6 `->;
infixr 6 `-->;
infix 4 `$;
infix 4 `$$;
infixr 5 `|->;
infixr 5 `|-->;

type vname = string;

datatype itype =
    IType of string * itype list
  | IFun of itype * itype
  | IVarT of vname * sort
    (*ML auxiliary*)
  | IDictT of (string * itype) list;

datatype ipat =
    ICons of (string * ipat list) * itype
  | IVarP of vname * itype;

datatype iexpr =
    IConst of string * itype
  | IVarE of vname * itype
  | IApp of iexpr * iexpr
  | IInst of iexpr * ClassPackage.sortlookup list list
  | IAbs of (vname * itype) * iexpr
  | ICase of iexpr * (ipat * iexpr) list
    (*ML auxiliary*)
  | IDictE of (string * iexpr) list
  | ILookup of (string list * vname);

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
    pattern                 p
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

fun map_itype f_itype (IType (tyco, tys)) =
      tyco `%% map f_itype tys
  | map_itype f_itype (IFun (t1, t2)) =
      f_itype t1 `-> f_itype t2
  | map_itype _ (ty as IVarT _) =
      ty;

fun map_ipat f_itype f_ipat (ICons ((c, ps), ty)) =
      ICons ((c, map f_ipat ps), f_itype ty)
  | map_ipat _ _ (p as IVarP _) =
      p;

fun map_iexpr f_itype f_ipat f_iexpr (IApp (e1, e2)) =
      f_iexpr e1 `$ f_iexpr e2
  | map_iexpr f_itype f_ipat f_iexpr (IInst (e, c)) =
      IInst (f_iexpr e, c)
  | map_iexpr f_itype f_ipat f_iexpr (IAbs (v, e)) =
      IAbs (v, f_iexpr e)
  | map_iexpr f_itype f_ipat f_iexpr (ICase (e, ps)) =
      ICase (f_iexpr e, map (fn (p, e) => (f_ipat p, f_iexpr e)) ps)
  | map_iexpr _ _ _ (e as IConst _) =
      e
  | map_iexpr _ _ _ (e as IVarE _) =
      e
  | map_iexpr f_itype f_ipat f_iexpr (IDictE ms) =
      IDictE (map (apsnd f_iexpr) ms)
  | map_iexpr _ _ _ (e as ILookup _) =
      e ;

fun fold_itype f_itype (IFun (t1, t2)) =
      f_itype t1 #> f_itype t2
  | fold_itype _ (ty as IType _) =
      I
  | fold_itype _ (ty as IVarT _) =
      I;

fun fold_ipat f_itype f_ipat (ICons ((_, ps), ty)) =
      f_itype ty #> fold f_ipat ps
  | fold_ipat f_itype f_ipat (p as IVarP _) =
      I;

fun fold_iexpr f_itype f_ipat f_iexpr (IApp (e1, e2)) =
      f_iexpr e1 #> f_iexpr e2
  | fold_iexpr f_itype f_ipat f_iexpr (IInst (e, c)) =
      f_iexpr e
  | fold_iexpr f_itype f_ipat f_iexpr (IAbs (v, e)) =
      f_iexpr e
  | fold_iexpr f_itype f_ipat f_iexpr (ICase (e, ps)) =
      f_iexpr e #> fold (fn (p, e) => f_ipat p #> f_iexpr e) ps
  | fold_iexpr _ _ _ (e as IConst _) =
      I
  | fold_iexpr _ _ _ (e as IVarE _) =
      I;


(* simple type matching *)

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


(* simple diagnosis *)

fun pretty_itype (IType (tyco, tys)) =
      Pretty.gen_list "" "(" ")" (Pretty.str tyco :: map pretty_itype tys)
  | pretty_itype (IFun (ty1, ty2)) =
      Pretty.gen_list "" "(" ")" [pretty_itype ty1, Pretty.str "->", pretty_itype ty2]
  | pretty_itype (IVarT (v, sort)) =
      Pretty.str (v ^ enclose "|" "|" (space_implode "|" sort))
  | pretty_itype (IDictT _) =
      Pretty.str "<DictT>";

fun pretty_ipat (ICons ((cons, ps), ty)) =
      Pretty.gen_list " " "(" ")"
        (Pretty.str cons :: map pretty_ipat ps @ [Pretty.str ":: ", pretty_itype ty])
  | pretty_ipat (IVarP (v, ty)) =
      Pretty.block [Pretty.str ("?" ^ v ^ "::"), pretty_itype ty];

fun pretty_iexpr (IConst (f, ty)) =
      Pretty.block [Pretty.str (f ^ "::"), pretty_itype ty]
  | pretty_iexpr (IVarE (v, ty)) =
      Pretty.block [Pretty.str ("?" ^ v ^ "::"), pretty_itype ty]
  | pretty_iexpr (IApp (e1, e2)) =
      Pretty.enclose "(" ")" [pretty_iexpr e1, Pretty.brk 1, pretty_iexpr e2]
  | pretty_iexpr (IInst (e, c)) =
      pretty_iexpr e
  | pretty_iexpr (IAbs ((v, ty), e)) =
      Pretty.enclose "(" ")" [Pretty.str ("?" ^ v ^ " |->"), Pretty.brk 1, pretty_iexpr e]
  | pretty_iexpr (ICase (e, cs)) =
      Pretty.enclose "(" ")" [
        Pretty.str "case ",
        pretty_iexpr e,
        Pretty.enclose "(" ")" (map (fn (p, e) =>
          Pretty.block [
            pretty_ipat p,
            Pretty.str " => ",
            pretty_iexpr e
          ]
        ) cs)
      ]
  | pretty_iexpr (IDictE _) =
      Pretty.str "<DictE>"
  | pretty_iexpr (ILookup (ls, v)) =
      Pretty.str ("<Lookup: " ^ commas ls ^ " in " ^ v ^ ">");


(* language auxiliary *)

fun itype_of_iexpr (IConst (_, ty)) = ty
  | itype_of_iexpr (IVarE (_, ty)) = ty
  | itype_of_iexpr (e as IApp (e1, e2)) = (case itype_of_iexpr e1
      of (IFun (ty2, ty')) =>
            if ty2 = itype_of_iexpr e2
            then ty'
            else error ("inconsistent application: in " ^ Pretty.output (pretty_iexpr e)
              ^ ", " ^ (Pretty.output o pretty_itype) ty2 ^ " vs. " ^ (Pretty.output o pretty_itype o itype_of_iexpr) e2)
       | _ => error ("expression is not a function: " ^ Pretty.output (pretty_iexpr e1)))
  | itype_of_iexpr (IInst (e, cs)) = itype_of_iexpr e
  | itype_of_iexpr (IAbs ((_, ty1), e2)) = ty1 `-> itype_of_iexpr e2
  | itype_of_iexpr (ICase ((_, [(_, e)]))) = itype_of_iexpr e;

fun itype_of_ipat (ICons (_, ty)) = ty
  | itype_of_ipat (IVarP (_, ty)) = ty;

fun ipat_of_iexpr (IConst (f, ty)) = ICons ((f, []), ty)
  | ipat_of_iexpr (IVarE v) = IVarP v
  | ipat_of_iexpr (e as IApp _) =
      (case unfold_app e
        of (IConst (f, ty), es) =>
              ICons ((f, map ipat_of_iexpr es), (snd o unfold_fun) ty)
         | (IInst (IConst (f, ty), _), es) =>
              ICons ((f, map ipat_of_iexpr es), (snd o unfold_fun) ty)
         | _ => error ("illegal expression for pattern: " ^ (Pretty.output o pretty_iexpr) e))
  | ipat_of_iexpr e =
      error ("illegal expression for pattern: " ^ (Pretty.output o pretty_iexpr) e);

fun tvars_of_itypes tys =
  let
    fun vars (IType (_, tys)) =
          fold vars tys
      | vars (IFun (ty1, ty2)) =
          vars ty1 #> vars ty2
      | vars (IVarT (v, _)) =
          insert (op =) v
  in fold vars tys [] end;

fun vars_of_ipats ps =
  let
    fun vars (ICons ((_, ps), _)) =
          fold vars ps
      | vars (IVarP (v, _)) =
          insert (op =) v
  in fold vars ps [] end;

fun vars_of_iexprs es =
  let
    fun vars (IConst (f, _)) =
          I
      | vars (IVarE (v, _)) =
          insert (op =) v
      | vars (IApp (e1, e2)) =
          vars e1 #> vars e2
      | vars (IAbs ((v, _), e)) =
          insert (op =) v
          #> vars e
      | vars (ICase (e, cs)) =
          vars e
          #> fold (fn (p, e) => fold (insert (op =)) (vars_of_ipats [p]) #> vars e) cs
      | vars (IInst (e, lookup)) =
          vars e
      | vars (IDictE ms) =
          fold (vars o snd) ms
      | vars (ILookup (_, v)) =
          cons v
  in fold vars es [] end;

fun instant_itype (v, sty) ty =
  let
    fun instant (IType (tyco, tys)) =
          tyco `%% map instant tys
      | instant (IFun (ty1, ty2)) =
          instant ty1 `-> instant ty2
      | instant (w as (IVarT (u, _))) =
          if v = u then sty else w
  in instant ty end;



(** language module system - definitions, modules, transactions **)

(* type definitions *)

datatype def =
    Nop
  | Fun of (ipat list * iexpr) list * (ClassPackage.sortcontext * itype)
  | Typesyn of (vname * string list) list * itype
  | Datatype of (vname * string list) list * (string * itype list) list * string list
  | Datatypecons of string
  | Class of class list * vname * (string * (ClassPackage.sortcontext * itype)) list * string list
  | Classmember of class
  | Classinst of class * (string * (vname * string list) list) * (string * string) list;

datatype node = Def of def | Module of node Graph.T;
type module = node Graph.T;
type transact = Graph.key list * module;
datatype 'dst transact_res = Succeed of 'dst | Fail of string list * exn option;
type 'dst transact_fin = 'dst transact_res * transact;
type ('src, 'dst) gen_exprgen = 'src -> transact -> 'dst transact_fin;
type gen_defgen = string -> transact -> (def * string list) transact_fin;
exception FAIL of string list * exn option;

val eq_def = (op =);

(* simple diagnosis *)

fun pretty_def Nop =
      Pretty.str "<NOP>"
  | pretty_def (Fun (eqs, (_, ty))) =
      Pretty.gen_list " |" "" "" (
        map (fn (ps, body) =>
          Pretty.block [
            Pretty.gen_list "," "[" "]" (map pretty_ipat ps),
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
  | pretty_def (Datatype (vs, cs, insts)) =
      Pretty.block [
        Pretty.list "(" ")" (map (pretty_itype o IVarT) vs),
        Pretty.str " |=> ",
        Pretty.gen_list " |" "" ""
          (map (fn (c, tys) => (Pretty.block o Pretty.breaks) (Pretty.str c :: map pretty_itype tys)) cs),
        Pretty.str ", instances ",
        Pretty.gen_list "," "[" "]" (map Pretty.str insts)
      ]
  | pretty_def (Datatypecons dtname) =
      Pretty.str ("cons " ^ dtname)
  | pretty_def (Class (supcls, v, mems, insts)) =
      Pretty.block [
        Pretty.str ("class var " ^ v ^ "extending "),
        Pretty.gen_list "," "[" "]" (map Pretty.str supcls),
        Pretty.str " with ",
        Pretty.gen_list "," "[" "]"
          (map (fn (m, (_, ty)) => Pretty.block [Pretty.str (m ^ "::"), pretty_itype ty]) mems),
        Pretty.str " instances ",
        Pretty.gen_list "," "[" "]" (map Pretty.str insts)
      ]
  | pretty_def (Classmember clsname) =
      Pretty.block [
        Pretty.str "class member belonging to ",
        Pretty.str clsname
      ]
  | pretty_def (Classinst (clsname, (tyco, arity), mems)) =
      Pretty.block [
        Pretty.str "class instance (",
        Pretty.str clsname,
        Pretty.str ", (",
        Pretty.str tyco,
        Pretty.str ", ",
        Pretty.gen_list "," "[" "]" (map (Pretty.gen_list "," "{" "}" o map Pretty.str o snd) arity),
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
          @ (the_list oo Option.mapPartial) ((fn Module modl' => SOME (pretty_deps modl') | _ => NONE) o Graph.get_node modl) (SOME key)
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

fun map_def name f =
  let
    val (modl, base) = dest_name name;
    fun mapp [] =
          Graph.map_node base (Def o f o dest_def)
      | mapp (m::ms) =
          Graph.map_node m (Module o mapp ms o dest_modl)
  in mapp modl end;

fun add_dep (name1, name2) modl =
  if name1 = name2 then modl
  else
    let
      val m1 = dest_name name1 |> apsnd single |> (op @);
      val m2 = dest_name name2 |> apsnd single |> (op @);
      val (ms, r1, r2) = get_prefix (op =) (m1, m2);
      val (ms, s1::r1, s2::r2) = get_prefix (op =) (m1, m2);
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

fun fold_map_defs f =
  let
    fun foldmap prfix (name, Def def) =
          apfst Def o f (NameSpace.pack (prfix @ [name]), def)
      | foldmap prfix (name, Module modl) =
          apfst Module o Graph.fold_map_nodes (foldmap (prfix @ [name])) modl
  in Graph.fold_map_nodes (foldmap []) end;

fun map_def_fun f_ipat f_iexpr (Fun (eqs, cty)) =
      Fun (map (fn (ps, rhs) => (map f_ipat ps, f_iexpr rhs)) eqs, cty)
  | map_def_fun _ _ def = def;

fun transform_defs f_def f_ipat f_iexpr s modl =
  let
    val (modl', s') = fold_map_defs f_def modl s
  in
    modl'
    |> map_defs (map_def_fun (f_ipat s') (f_iexpr s'))
  end;

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
    |> select (fold (mk_ipath o dest_name) (filter NameSpace.is_qualified names) (PN ([], [])))
    |> dest_modl
  end;

fun (*add_check_transform (name, (Datatypecons dtname)) =
      (debug 7 (fn _ => "transformation for datatype constructor " ^ quote name
        ^ " of datatype " ^ quote dtname) ();
      ([([dtname],
          fn [Datatype (_, _, [])] => NONE
            | _ => "attempted to add constructor to already instantiating datatype" |> SOME)],
       [(dtname,
          fn Datatype (vs, cs, insts) => Datatype (vs, name::cs, insts)
           | def => "attempted to add datatype constructor to non-datatype: "
              ^ (Pretty.output o pretty_def) def |> error)])
      )
  | add_check_transform (name, Classmember (clsname, v, ty)) =
      let
        val _ = debug 7 (fn _ => "transformation for class member " ^ quote name
        ^ " of class " ^ quote clsname) ();
        fun check_var (IType (tyco, tys)) s =
              fold check_var tys s
          | check_var (IFun (ty1, ty2)) s =
              s
              |> check_var ty1
              |> check_var ty2
          | check_var (IVarT (w, sort)) s =
              if v = w
              andalso member (op =) sort clsname
              then "additional class appears at type variable" |> SOME
              else NONE
      in
        ([([], fn [] => check_var ty NONE),
          ([clsname],
             fn [Class (_, _, _, [])] => NONE
              | _ => "attempted to add class member to witnessed class" |> SOME)],
         [(clsname,
             fn Class (supcs, v, mems, insts) => Class (supcs, v, name::mems, insts)
              | def => "attempted to add class member to non-class"
                 ^ (Pretty.output o pretty_def) def |> error)])
      end
  | *) add_check_transform (name, Classinst (clsname, (tyco, arity), memdefs)) =
      let
        val _ = debug 7 (fn _ => "transformation for class instance " ^ quote tyco
          ^ " of class " ^ quote clsname) ();
        (* fun check [Classmember (_, v, mtyp_c), Fun (_, (_, mtyp_i))] =
              let
                val mtyp_i' = instant_itype (v, tyco `%% map IVarT arity) mtyp_c;
              in if eq_itype (mtyp_i', mtyp_i)
                then NONE
                else "wrong type signature for class member: "
                  ^ (Pretty.output o pretty_itype) mtyp_i' ^ " expected, "
                  ^ (Pretty.output o pretty_itype) mtyp_i ^ " given" |> SOME
              end
          | check defs =
              "non-well-formed definitions encountered for classmembers: "
              ^ (commas o map (quote o Pretty.output o pretty_def)) defs |> SOME *)
      in
        ((* map (fn (memname, memprim) => ([memname, memprim], check)) memdefs*) [],
          [(clsname,
              fn Class (supcs, v, mems, insts) => Class (supcs, v, mems, name::insts)
               | def => "attempted to add class instance to non-class"
                  ^ (Pretty.output o pretty_def) def |> error),
           (tyco,
              fn Datatype (vs, cs, insts) => Datatype (vs, cs, name::insts)
               | Nop => Nop
               | def => "attempted to instantiate non-type to class instance"
                  ^ (Pretty.output o pretty_def) def |> error)])
      end
  | add_check_transform _ = ([], []);

(* checks to be implemented here lateron:
    - well-formedness of function equations
    - only possible to add defined constructors and class members
    - right type abstraction with class members
    - correct typing of instance definitions
*)

fun succeed some = pair (Succeed some);
fun fail msg = pair (Fail ([msg], NONE));

fun check_fail _ (Succeed dst, trns) = (dst, trns)
  | check_fail msg (Fail (msgs, e), _) = raise FAIL (msg::msgs, e);

fun select_generator _ _ [] modl =
      ([], modl) |> fail ("no code generator available")
  | select_generator mk_msg src gens modl =
      let
        fun handle_fail msgs f =
          let
            in
              if ! soft_exc
              then
                ([], modl) |> f
                handle FAIL exc => (Fail exc, ([], modl))
                     | e => (Fail (msgs, SOME e), ([], modl))
              else
                ([], modl) |> f
                handle FAIL exc => (Fail exc, ([], modl))
            end;
        fun select msgs [(gname, gen)] =
          handle_fail (msgs @ [mk_msg gname]) (gen src)
        fun select msgs ((gname, gen)::gens) =
          let
            val msgs' = msgs @ [mk_msg gname]
          in case handle_fail msgs' (gen src)
          of (Fail (_, NONE), _) =>
               select msgs' gens
           | result =>
               result
          end;
      in select [] gens end;

fun gen_invoke codegens msg src (deps, modl) =
  modl
  |> select_generator (fn gname => "trying code generator " ^ gname ^ " for source " ^ quote msg)
       src codegens
  |> check_fail msg
  ||> (fn (deps', modl') => (append deps' deps, modl'));

fun gen_ensure_def defgens msg name (deps, modl) =
  let
    fun add (name, def) (deps, modl) =
      let
        val (checks, trans) = add_check_transform (name, def);
        fun check (check_defs, checker) modl =
          let
            fun get_def' s =
              if NameSpace.is_qualified s
              then get_def modl s
              else Nop
            val defs =
              check_defs
              |> map get_def';
          in
            case checker defs
             of NONE => modl
              | SOME msg => raise FAIL ([msg], NONE)
          end;
        fun transform (name, f) modl =
          modl
          |> debug 9 (fn _ => "transforming node " ^ name)
          |> (if NameSpace.is_qualified name then map_def name f else I);
      in
        modl
        |> debug 10 (fn _ => "considering addition of " ^ name
             ^ " := " ^ (Pretty.output o pretty_def) def)
        |> debug 10 (fn _ => "consistency checks")
        |> fold check checks
        |> debug 10 (fn _ => "dependencies")
        |> fold (curry add_dep name) deps
        |> debug 10 (fn _ => "adding")
        |> map_def name (fn _ => def)
        |> debug 10 (fn _ => "transforming")
        |> fold transform trans
        |> debug 10 (fn _ => "adding done")
      end;
    fun ensure_node name modl =
      (debug 9 (fn _ => "testing node " ^ quote name) ();
      if can (get_def modl) name
      then
        modl
        |> debug 9 (fn _ => "asserting node " ^ quote name)
        |> pair [name]
      else
        modl
        |> debug 9 (fn _ => "creating node " ^ quote name)
        |> add_def (name, Nop)
        |> select_generator (fn gname => "trying code generator " ^ gname ^ " for definition of " ^ quote name)
             name defgens
        |> check_fail msg
        |-> (fn (def, names') =>
           add (name, def)
           #> fold_map ensure_node names')
        |-> (fn names' => pair (name :: Library.flat names'))
      )
  in
    modl
    |> ensure_node name
    |-> (fn names => pair (names@deps))
  end;

fun start_transact f modl =
  let
    fun handle_fail f modl =
      ((([], modl) |> f)
      handle FAIL (msgs, NONE) =>
        (error o cat_lines) ("code generation failed, while:" :: msgs))
      handle FAIL (msgs, SOME e) =>
        ((writeln o cat_lines) ("code generation failed, while:" :: msgs); raise e);
  in
    modl
    |> handle_fail f
    |-> (fn x => fn (_, module) => (x, module))
  end;


(** primitive language constructs **)

val class_eq = "Eq"; (*defined for all primitve types and extensionally for all datatypes*)
val type_bool = "Bool";
val type_integer = "Integer"; (*infinite!*)
val type_float = "Float";
val type_pair = "Pair";
val type_list = "List";
val cons_true = "True";
val cons_false = "False";
val cons_not = "not";
val cons_pair = "Pair";
val cons_nil = "Nil";
val cons_cons = "Cons";
val fun_eq = "eq"; (*to class eq*)
val fun_not = "not";
val fun_and = "and";
val fun_or = "or";
val fun_if = "if";
val fun_fst = "fst";
val fun_snd = "snd";
val fun_add = "add";
val fun_mult = "mult";
val fun_minus = "minus";
val fun_lt = "lt";
val fun_le = "le";
val fun_wfrec = "wfrec";

local

val A = IVarT ("a", []);
val B = IVarT ("b", []);
val E = IVarT ("e", [class_eq]);

in

val Type_bool = type_bool `%% [];
val Type_integer = type_integer `%% [];
val Type_float = type_float `%% [];
fun Type_pair a b = type_pair `%% [a, b];
fun Type_list a = type_list `%% [a];
val Cons_true = IConst (cons_true, Type_bool);
val Cons_false = IConst (cons_false, Type_bool);
val Cons_pair = IConst (cons_pair, A `-> B `-> Type_pair A B);
val Cons_nil = IConst (cons_nil, Type_list A);
val Cons_cons = IConst (cons_cons, A `-> Type_list A `-> Type_list A);
val Fun_eq = IConst (fun_eq, E `-> E `-> Type_bool);
val Fun_not = IConst (fun_not, Type_bool `-> Type_bool);
val Fun_and = IConst (fun_and, Type_bool `-> Type_bool `-> Type_bool);
val Fun_or = IConst (fun_or, Type_bool `-> Type_bool `-> Type_bool);
val Fun_if = IConst (fun_if, Type_bool `-> A `-> A `-> A);
val Fun_fst = IConst (fun_fst, Type_pair A B `-> A);
val Fun_snd = IConst (fun_snd, Type_pair A B `-> B);
val Fun_0 = IConst ("0", Type_integer);
val Fun_1 = IConst ("1", Type_integer);
val Fun_add = IConst (fun_add, Type_integer `-> Type_integer `-> Type_integer);
val Fun_mult = IConst (fun_mult, Type_integer `-> Type_integer `-> Type_integer);
val Fun_minus = IConst (fun_minus, Type_integer `-> Type_integer);
val Fun_lt = IConst (fun_lt, Type_integer `-> Type_integer `-> Type_bool);
val Fun_le = IConst (fun_le, Type_integer `-> Type_integer `-> Type_bool);
val Fun_wfrec = IConst (fun_wfrec, ((A `-> B) `-> A `-> B) `-> A `-> B);

fun foldl1 f (x::xs) =
  Library.foldl f (x, xs);
val ** = foldl1 (uncurry Type_pair);
val XXp = foldl1 (fn (a, b) =>
  let
    val ty_a = itype_of_ipat a;
    val ty_b = itype_of_ipat b;
  in ICons ((cons_pair, [a, b]), Type_pair ty_a ty_b) end);
val XXe = foldl1 (fn (a, b) =>
  let
    val ty_a = itype_of_iexpr a;
    val ty_b = itype_of_iexpr b;
  in IConst (cons_pair, ty_a `-> ty_b `-> Type_pair ty_a ty_b) `$ a `$ b end);

end; (* local *)

val prims = [class_eq, type_bool, type_integer, type_float, type_pair, type_list,
  cons_true, cons_false, cons_pair, cons_nil, cons_cons, fun_eq, fun_not, fun_and,
  fun_or, fun_if, fun_fst, fun_snd, fun_add, fun_mult, fun_minus, fun_lt, fun_le, fun_wfrec];


(** equality handling **)

fun invoke_eq gen_ty gen_eq x (trns as (_ , modl)) =
  let
    fun mk_eqpred dtname =
      let
        val (vs, cons, _) = case get_def modl dtname of Datatype info => info;
        val arity = map (rpair [class_eq] o fst) vs
        val ty = IType (dtname, map IVarT arity);
        fun mk_eq (c, []) =
              ([ICons ((c, []), ty), ICons ((c, []), ty)], Cons_true)
          | mk_eq (c, tys) =
              let
                val vars1 = Term.invent_names [] "a" (length tys);
                val vars2 = Term.invent_names vars1 "b" (length tys);
                fun mk_eq_cons ty' (v1, v2) =
                  IConst (fun_eq, ty' `-> ty' `-> Type_bool) `$ IVarE (v1, ty) `$ IVarE (v2, ty)
                fun mk_conj (e1, e2) =
                  Fun_and `$ e1 `$ e2;
              in
                ([ICons ((c, map2 (curry IVarP) vars1 tys), ty),
                  ICons ((c, map2 (curry IVarP) vars2 tys), ty)],
                  foldr1 mk_conj (map2 mk_eq_cons tys (vars1 ~~ vars2)))
              end;
        val eqs = map mk_eq cons @ [([IVarP ("_", ty), IVarP ("_", ty)], Cons_false)];
      in
        (Fun (eqs, (arity, ty `-> ty `-> Type_bool)), arity)
      end;
    fun invoke' (IType (tyco, tys)) trns =
          trns
          |> fold_map invoke' tys
          |-> (fn is_eq =>
                if forall I is_eq
                  then if NameSpace.is_qualified tyco
                  then
                    gen_eq (tyco, mk_eqpred tyco)
                    #> pair true
                  else
                    pair true
                else
                  pair false)
      | invoke' (IFun _) trns =
          trns 
          |> pair false
      | invoke' (IVarT (_, sort)) trns =
          trns 
          |> pair (member (op =) sort class_eq)
  in
    trns
    |> gen_ty x
    |-> (fn ty => invoke' ty)
  end;


(** generic transformation **)

fun extract_defs e =
  let
    fun extr_itype (ty as IType (tyco, _)) =
          cons tyco #> fold_itype extr_itype ty
      | extr_itype ty =
          fold_itype extr_itype ty
    fun extr_ipat (p as ICons ((c, _), _)) =
          cons c #> fold_ipat extr_itype extr_ipat p
      | extr_ipat p =
          fold_ipat extr_itype extr_ipat p
    fun extr_iexpr (e as IConst (f, _)) =
          cons f #> fold_iexpr extr_itype extr_ipat extr_iexpr e
      | extr_iexpr e =
          fold_iexpr extr_itype extr_ipat extr_iexpr e
  in extr_iexpr e [] end;

fun eta_expand query =
  let
    fun eta_app ((f, ty), es) =
      let
        val delta = query f - length es;
        val add_n = if delta < 0 then 0 else delta;
        val tys =
          (fst o unfold_fun) ty
          |> curry Library.drop (length es)
          |> curry Library.take add_n
        val add_vars =
          Term.invent_names (vars_of_iexprs es) "x" add_n ~~ tys;
      in
        Library.foldr IAbs (add_vars, IConst (f, ty) `$$ es `$$ (map IVarE add_vars))
      end;
    fun eta_iexpr' e = map_iexpr I I eta_iexpr e
    and eta_iexpr (IConst (f, ty)) =
          eta_app ((f, ty), [])
      | eta_iexpr (e as IApp _) =
          (case (unfold_app e)
           of (IConst (f, ty), es) =>
                eta_app ((f, ty), map eta_iexpr es)
            | _ => eta_iexpr' e)
      | eta_iexpr e = eta_iexpr' e;
  in map_defs (map_def_fun I eta_iexpr) end;

val eta_expand_poly =
  let
    fun map_def_fun (def as Fun ([([], e)], cty as (sortctxt, (ty as IFun (ty1, ty2))))) =
          if (not o null) sortctxt
            orelse (null o tvars_of_itypes) [ty]
          then def
          else
            let
              val add_var = (hd (Term.invent_names (vars_of_iexprs [e]) "x" 1), ty1)
            in (Fun ([([IVarP add_var], IAbs (add_var, e))], cty)) end
      | map_def_fun def = def;
  in map_defs map_def_fun end;

fun tupelize_cons module =
  let
    fun replace_cons (cons as (_, [])) =
          pair cons
      | replace_cons (cons as (_, [_])) =
          pair cons
      | replace_cons (con, tys) =
          cons con
          #> pair (con, [** tys])
    fun replace_def (_, (def as Datatype (vs, cs, insts))) =
          fold_map replace_cons cs
          #-> (fn cs => pair (Datatype (vs, cs, insts)))
      | replace_def (_, def) =
          pair def
    fun replace_app cs ((f, ty), es) =
      if member (op =) cs f
      then
        let
          val (tys, ty') = unfold_fun ty
        in IConst (f, ** tys `-> ty') `$ XXe es end
      else IConst (f, ty) `$$ es;
    fun replace_iexpr cs (IConst (f, ty)) =
          replace_app cs ((f, ty), [])
      | replace_iexpr cs (e as IApp _) =
          (case unfold_app e
           of (IConst fty, es) => replace_app cs (fty, map (replace_iexpr cs) es)
            | _ => map_iexpr I I (replace_iexpr cs) e)
      | replace_iexpr cs e = map_iexpr I I (replace_iexpr cs) e;
    fun replace_ipat cs (p as ICons ((c, ps), ty)) =
          if member (op =) cs c then
            ICons ((c, [XXp (map (replace_ipat cs) ps)]), ty)
          else map_ipat I (replace_ipat cs) p
      | replace_ipat cs p = map_ipat I (replace_ipat cs) p;
  in
    transform_defs replace_def replace_ipat replace_iexpr [cons_cons] module
  end;

fun eliminate_classes module =
  let
    fun transform_itype (IVarT (v, s)) =
          IVarT (v, [])
      | transform_itype (ty as IDictT _) =
          ty
      | transform_itype ty =
          map_itype transform_itype ty;
    fun transform_ipat p =
          map_ipat transform_itype transform_ipat p;
    fun transform_iexpr vname_alist (IInst (e, ls)) =
          let
            fun transform_lookup (ClassPackage.Instance ((cdict, idict), ls)) =
                  ls
                  |> transform_lookups
                  |-> (fn tys =>
                        curry mk_apps (IConst (idict, cdict `%% tys))
                        #> pair (cdict `%% tys))
              | transform_lookup (ClassPackage.Lookup (deriv, (v, i))) =
                  let
                    val (v', cls) =
                      (nth o the oo AList.lookup (op =)) vname_alist v i;
                    fun mk_parm tyco = tyco `%% [IVarT (v, [])];
                  in (mk_parm cls, ILookup (deriv, v')) end
            and transform_lookups lss =
                  map_yield (map_yield transform_lookup
                       #> apfst **
                       #> apsnd XXe) lss
          in transform_iexpr vname_alist e `$$ (snd o transform_lookups) ls end
      | transform_iexpr vname_alist e =
          map_iexpr transform_itype transform_ipat (transform_iexpr vname_alist) e;
    fun mk_cls_typ_map v membrs ty_inst =
      map (fn (m, (mctxt, ty)) =>
        (m, ty |> instant_itype (v, ty_inst))) membrs;
    fun extract_members (cls, Class (supclss, v, membrs, _)) =
          let
            val ty_cls = cls `%% [IVarT (v, [])];
            val w = "d";
            val add_supclss = if null supclss then I else cons (v, supclss);
            fun mk_fun (m, (mctxt, ty)) = (m, Fun ([([IVarP (w, ty_cls)], ILookup ([m], w))],
              (add_supclss mctxt, ty `-> ty_cls)));
          in fold (cons o mk_fun) membrs end
      | extract_members _ = I;
    fun introduce_dicts (Class (supcls, v, membrs, insts)) =
          let
            val _ = writeln "TRANSFORMING CLASS";
            val _ = print (Class (supcls, v, membrs, insts));
            val varname_cls = Term.invent_names (tvars_of_itypes (map (snd o snd) membrs)) "a" 1 |> hd
          in
            Typesyn ([(varname_cls, supcls)], IDictT (mk_cls_typ_map v membrs (IVarT (varname_cls, []))))
          end
      | introduce_dicts (Classinst (clsname, (tyco, arity), memdefs)) =
          let
            val _ = writeln "TRANSFORMING CLASSINST";
            val _ = print (Classinst (clsname, (tyco, arity), memdefs));
            val Class (_, v, members, _) =
              if clsname = class_eq
              then
                Class ([], "a", [(fun_eq, ([], IVarT ("a", []) `-> IVarT ("a", []) `-> Type_bool))], [])
              else
                get_def module clsname;
            val ty = tyco `%% map IVarT arity;
            val inst_typ_map = mk_cls_typ_map v members ty;
            val memdefs_ty = map (fn (memname, memprim) =>
              (memname, (memprim, (the o AList.lookup (op =) inst_typ_map) memname))) memdefs;
          in
            Fun ([([], IDictE (map (apsnd IConst) memdefs_ty))],
              ([], IType (clsname, [ty])))
          end
      | introduce_dicts d = d;
    fun elim_sorts (Fun (eqs, ([], ty))) =
          (writeln "TRANSFORMING FUN ()";
          Fun (map (fn (ps, rhs) => (map transform_ipat ps, transform_iexpr [] rhs)) eqs,
            ([], transform_itype ty)))
      | elim_sorts (Fun (eqs, (sortctxt, ty))) =
          let
            val _ = writeln "TRANSFORMING FUN (1)";
            val varnames_ctxt =
              dig
                (Term.invent_names ((vars_of_iexprs o map snd) eqs @
                  (vars_of_ipats o Library.flat o map fst) eqs) "d" o length)
                (map snd sortctxt);
            val _ = writeln "TRANSFORMING FUN (2)";
            val vname_alist = map2 (fn (vt, sort) => fn vs => (vt, vs ~~ sort))
              sortctxt varnames_ctxt |> print;
            val _ = writeln "TRANSFORMING FUN (3)";
            val ty' = map (op ** o (fn (vt, vss) => map (fn (_, cls) =>
              cls `%% [IVarT (vt, [])]) vss)) vname_alist
              `--> transform_itype ty;
            val _ = writeln "TRANSFORMING FUN (4)";
            val ps_add = map (XXp o (fn (vt, vss) => map (fn (v, cls) =>
              IVarP (v, cls `%% [IVarT (vt, [])])) vss)) vname_alist;
            val _ = writeln "TRANSFORMING FUN (5)";
          in Fun (map (fn (ps, rhs) => (ps_add @ map transform_ipat ps, transform_iexpr vname_alist rhs)) eqs, ([], ty')) before writeln "TRANSFORMING FUN (6)" end
      | elim_sorts (Datatype (vars, constrs, insts)) =
          (writeln "TRANSFORMING DATATYPE (1)";
          Datatype (map (fn (v, _) => (v, [])) vars, map (apsnd (map transform_itype)) constrs, insts)
          before writeln "TRANSFORMING DATATYPE (2)")
      | elim_sorts (Typesyn (vars, ty)) =
          (writeln "TRANSFORMING TYPESYN (1)";
          Typesyn (map (fn (v, _) => (v, [])) vars, transform_itype ty)
          before writeln "TRANSFORMING TYPESYN (2)")
      | elim_sorts d = d;
  in
    module
    |> `(fn module => fold_defs extract_members module [])
    |-> (fn membrs => fold (fn (name, f) => map_def name (K f)) membrs)
    |> map_defs introduce_dicts
    |> map_defs elim_sorts
  end;


(** generic serialization **)

(* resolving *)

fun mk_resolvtab nspgrp validate module =
  let
    fun ensure_unique prfix prfix' name name' (locals, tab) =
      let
        fun uniquify name n =
          let
            val name' = if n = 0 then name else name ^ "_" ^ string_of_int n
          in
            if member (op =) locals name'
            then uniquify name (n+1)
            else case validate name
              of NONE => name'
               | SOME name' => uniquify name' n
          end;
        val name'' = uniquify name' 0;
      in
        (locals, tab)
        |> apsnd (Symtab.update_new
             (NameSpace.pack (prfix @ [name]), NameSpace.pack (prfix' @ [name''])))
        |> apfst (cons name'')
        |> pair name''
      end;
    fun fill_in prfix prfix' node tab =
      let
        val keys = Graph.keys node;
        val nodes = AList.make (Graph.get_node node) keys;
        val (mods, defs) =
          nodes
          |> List.partition (fn (_, Module _) => true | _ => false)
          |> apfst (map (fn (name, Module m) => (name, m)))
          |> apsnd (map fst)
        fun modl_validate (name, modl) (locals, tab) =
          (locals, tab)
          |> ensure_unique prfix prfix' name name
          |-> (fn name' => apsnd (fill_in (prfix @ [name]) (prfix @ [name']) modl))
        fun ensure_unique_sidf sidf =
          let
            val [shallow, name] = NameSpace.unpack sidf;
          in
            nspgrp
            |> get_first
                (fn grp => if member (op =) grp shallow
                  then grp |> remove (op =) shallow |> SOME else NONE)
            |> these
            |> map (fn s => NameSpace.pack [s, name])
            |> exists (member (op =) defs)
            |> (fn b => if b then sidf else name)
          end;
        fun def_validate sidf (locals, tab) =
          (locals, tab)
          |> ensure_unique prfix prfix' sidf (ensure_unique_sidf sidf)
          |> snd
      in
        ([], tab)
        |> fold modl_validate mods
        |> fold def_validate defs
        |> snd
      end;
  in
    Symtab.empty
    |> fill_in [] [] module
  end;

fun mk_resolv tab =
  let
    fun resolver modl name =
      if NameSpace.is_qualified name then
        let
          val _ = debug 12 (fn name' => "resolving " ^ quote name ^ " in " ^ (quote o NameSpace.pack) modl) ();
          val modl' = if null modl then [] else (NameSpace.unpack o the o Symtab.lookup tab o NameSpace.pack) modl;
          val name' = (NameSpace.unpack o the o Symtab.lookup tab) name
        in
          (NameSpace.pack o #3 o get_prefix (op =)) (modl', name')
          |> debug 12 (fn name' => "resolving " ^ quote name ^ " to " ^ quote name' ^ " in " ^ (quote o NameSpace.pack) modl)
        end
      else name
  in resolver end;


(* serialization *)

fun serialize s_def s_module validate nspgrp name_root module =
  let
    val _ = debug 15 (fn _ => "serialize 1") ();
    val resolvtab = mk_resolvtab nspgrp validate module;
    val _ = debug 15 (fn _ => "serialize 2") ();
    val resolver = mk_resolv resolvtab;
    val _ = debug 15 (fn _ => "serialize 3") ();
    fun seri prfx ([(name, Module module)]) =
          (debug 15 (fn _ => "serializing module " ^ quote name) ();
          s_module (resolver prfx (prfx @ [name] |> NameSpace.pack),
            List.mapPartial (seri (prfx @ [name]))
              ((map (AList.make (Graph.get_node module)) o rev o Graph.strong_conn) module))
          |> SOME)
      | seri prfx ds =
          (debug 15 (fn _ => "serializing definitions " ^ (commas o map fst) ds) ();
          s_def (resolver prfx) (map
            (fn (name, Def def) => (resolver prfx (prfx @ [name] |> NameSpace.pack), def)) ds))
  in
    setmp print_mode [] (fn _ => s_module (name_root, (List.mapPartial (seri [])
      ((map (AList.make (Graph.get_node module)) o rev o Graph.strong_conn) module)))) ()
  end;

end; (* struct *)


structure CodegenThingol : CODEGEN_THINGOL =
struct

open CodegenThingolOp;

end; (* struct *)
