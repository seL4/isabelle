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
  val eq_itype: itype * itype -> bool
  val eq_ipat: ipat * ipat -> bool
  val eq_iexpr: iexpr * iexpr -> bool
  val mk_funs: itype list * itype -> itype;
  val mk_apps: iexpr * iexpr list -> iexpr;
  val pretty_itype: itype -> Pretty.T;
  val pretty_ipat: ipat -> Pretty.T;
  val pretty_iexpr: iexpr -> Pretty.T;
  val unfold_fun: itype -> itype list * itype;
  val unfold_app: iexpr -> iexpr * iexpr list;
  val unfold_let: iexpr -> (ipat * iexpr) list * iexpr;
  val itype_of_iexpr: iexpr -> itype;
  val itype_of_ipat: ipat -> itype;
  val ipat_of_iexpr: iexpr -> ipat;
  val vars_of_ipats: ipat list -> vname list;
  val instant_itype: vname * itype -> itype -> itype;
  val invent_var_t_names: itype list -> int -> vname list -> vname -> vname list;
  val invent_var_e_names: iexpr list -> int -> vname list -> vname -> vname list;

  datatype def =
      Nop
    | Fun of (ipat list * iexpr) list * (ClassPackage.sortcontext * itype)
    | Typesyn of (vname * string list) list * itype
    | Datatype of (vname * string list) list * string list * string list
    | Datatypecons of string * itype list
    | Class of string list * string list * string list
    | Classmember of string * vname * itype
    | Classinst of string * (string * string list list) * (string * string) list;
  type module;
  type transact;
  type 'dst transact_fin;
  type ('src, 'dst) gen_codegen = 'src -> transact -> 'dst transact_fin;
  type gen_defgen = string -> transact -> (def * string list) transact_fin;
  val eq_def: def * def -> bool;
  val pretty_def: def -> Pretty.T;
  val pretty_module: module -> Pretty.T;  
  val empty_module: module;
  val get_def: module -> string -> def;
  val merge_module: module * module -> module;
  val partof: string list -> module -> module;
  val succeed: 'a -> transact -> 'a transact_fin;
  val fail: string -> transact -> 'a transact_fin;
  val gen_invoke: (string * ('src, 'dst) gen_codegen) list -> string
    -> 'src -> transact -> 'dst * transact;
  val gen_ensure_def: (string * gen_defgen) list -> string
    -> string -> transact -> transact;

  val prims: string list;
  val extract_defs: iexpr -> string list;
  val eta_expand: (string -> int) -> module -> module;
  val connect_datatypes_clsdecls: module -> module;
  val tupelize_cons: module -> module;
  val eliminate_dtconstr: module -> module;
  val eliminate_classes: module -> module;

  val debug_level : int ref;
  val debug : int -> ('a -> string) -> 'a -> 'a;
end;

signature CODEGEN_THINGOL_OP =
sig
  include CODEGEN_THINGOL;
  val `%% : string * itype list -> itype;
  val `-> : itype * itype -> itype;
  val `--> : itype list * itype -> itype;
  val `$ : iexpr * iexpr -> iexpr;
  val `$$ : iexpr * iexpr list -> iexpr;
end;


structure CodegenThingolOp: CODEGEN_THINGOL_OP =
struct

(** auxiliary **)

val debug_level = ref 0;
fun debug d f x = (if d <= !debug_level then Output.debug (f x) else (); x);

fun foldl' f (l, []) = the l
  | foldl' f (_, (r::rs)) =
      let
        fun itl (l, [])  = l
          | itl (l, r::rs) = itl (f (l, r), rs)
      in itl (r, rs) end;

fun foldr' f ([], r) = the r
  | foldr' f (ls, _) =
      let
        fun itr [l] = l
          | itr (l::ls) = f (l, itr ls)
      in itr ls end;

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

val eq_itype = (op =);
val eq_ipat = (op =);
val eq_iexpr = (op =);

val mk_funs = Library.foldr IFun;
val mk_apps = Library.foldl IApp;

fun tyco `%% tys = IType (tyco, tys);
val op `-> = IFun;
fun f `$ x = IApp (f, x);
val op `--> = mk_funs;
val op `$$ = mk_apps;

val unfold_fun = unfoldr
  (fn IFun t => SOME t
    | _ => NONE);

val unfold_app = unfoldl
  (fn IApp e => SOME e
    | _ => NONE);

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
      e;

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


(* simple diagnosis *)

fun pretty_itype (IType (tyco, tys)) =
      Pretty.gen_list "" "(" ")" (Pretty.str tyco :: map pretty_itype tys)
  | pretty_itype (IFun (ty1, ty2)) =
      Pretty.gen_list "" "(" ")" [pretty_itype ty1, Pretty.str "->", pretty_itype ty2]
  | pretty_itype (IVarT (v, sort)) =
      Pretty.str (v ^ enclose "|" "|" (space_implode "|" sort))

fun pretty_ipat (ICons ((cons, ps), ty)) =
      Pretty.gen_list " " "(" ")"
        (Pretty.str cons :: map pretty_ipat ps @ [Pretty.str ":: ", pretty_itype ty])
  | pretty_ipat (IVarP (v, ty)) =
      Pretty.block [Pretty.str ("?" ^ v ^ "::"), pretty_itype ty]

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
  | itype_of_iexpr (IInst (e, cs)) = error ""
  | itype_of_iexpr (IAbs ((_, ty1), e2)) = ty1 `-> itype_of_iexpr e2
  | itype_of_iexpr (ICase ((_, [(_, e)]))) = itype_of_iexpr e;

fun itype_of_ipat (ICons (_, ty)) = ty
  | itype_of_ipat (IVarP (_, ty)) = ty

fun ipat_of_iexpr (IConst (f, ty)) = ICons ((f, []), ty)
  | ipat_of_iexpr (IVarE v) = IVarP v
  | ipat_of_iexpr (e as IApp _) =
      case unfold_app e of (IConst (f, ty), es) =>
        ICons ((f, map ipat_of_iexpr es), (snd o unfold_fun) ty);

fun vars_of_ipats ps =
  let
    fun vars (ICons ((_, ps), _)) = fold vars ps
      | vars (IVarP (v, _)) = cons v
  in fold vars ps [] end;

fun instant_itype (v, sty) ty =
  let
    fun instant (IType (tyco, tys)) =
          tyco `%% map instant tys
      | instant (IFun (ty1, ty2)) =
          instant ty1 `-> instant ty2
      | instant (w as (IVarT (u, _))) =
          if v = u then sty else w
  in instant ty end;

fun invent_var_t_names tys n used a =
  let
    fun invent (IType (_, tys)) =
          fold invent tys
      | invent (IFun (ty1, ty2)) =
          invent ty1 #> invent ty2
      | invent (IVarT (v, _)) =
          cons v
in Term.invent_names (fold invent tys used) a n end;

fun invent_var_e_names es n used a =
  let
    fun invent (IConst (f, _)) =
          I
      | invent (IVarE (v, _)) =
          cons v
      | invent (IApp (e1, e2)) =
          invent e1 #> invent e2
      | invent (IAbs ((v, _), e)) =
          cons v #> invent e
      | invent (ICase (e, cs)) =
          invent e
          #>
          fold (fn (p, e) => append (vars_of_ipats [p]) #> invent e) cs
  in Term.invent_names (fold invent es used) a n end;


(** language module system - definitions, modules, transactions **)



(* type definitions *)

datatype def =
    Nop
  | Fun of (ipat list * iexpr) list * (ClassPackage.sortcontext * itype)
  | Typesyn of (vname * string list) list * itype
  | Datatype of (vname * string list) list * string list * string list
  | Datatypecons of string * itype list
  | Class of string list * string list * string list
  | Classmember of string * string * itype
  | Classinst of string * (string * string list list) * (string * string) list;

datatype node = Def of def | Module of node Graph.T;
type module = node Graph.T;
type transact = Graph.key list * module;
datatype 'dst transact_res = Succeed of 'dst | Fail of string;
type 'dst transact_fin = 'dst transact_res * transact;
type ('src, 'dst) gen_codegen = 'src -> transact -> 'dst transact_fin;
type gen_defgen = string -> transact -> (def * string list) transact_fin;
exception FAIL of string;

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
  | pretty_def (Datatype (vs, cs, clss)) =
      Pretty.block [
        Pretty.list "(" ")" (map (pretty_itype o IVarT) vs),
        Pretty.str " |=> ",
        Pretty.gen_list " |" "" "" (map Pretty.str cs),
        Pretty.str ", instance of ",
        Pretty.gen_list "," "[" "]" (map Pretty.str clss)
      ]
  | pretty_def (Datatypecons (dtname, tys)) =
      Pretty.block [
        Pretty.str "cons ",
        Pretty.gen_list " ->" "" "" (map pretty_itype tys @ [Pretty.str dtname])
      ]
  | pretty_def (Class (supcls, mems, insts)) =
      Pretty.str "Class ..."
  | pretty_def (Classmember (cls, v, ty)) =
      Pretty.str "Classmember ..."
  | pretty_def (Classinst (cls, insts, mems)) =
      Pretty.str "Classinst ..."

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

fun add_check_transform (name, (Datatypecons (dtname, _))) =
      ([([dtname],
          fn [Datatype (_, _, [])] => NONE | _ => "attempted to add constructor to already instantiating datatype" |> SOME)],
       [(dtname,
          fn Datatype (vs, cs, clss) => Datatype (vs, name::cs, clss)
           | def => "attempted to add datatype constructor to non-datatype: "
              ^ (Pretty.output o pretty_def) def |> error)])
  | add_check_transform (name, Classmember (clsname, v, ty)) =
      let
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
             fn [Class (_, _, [])] => NONE
              | _ => "attempted to add class member to witnessed class" |> SOME)],
         [(clsname,
             fn Class (supcs, mems, insts) => Class (supcs, name::mems, insts)
              | def => "attempted to add class member to non-class"
                 ^ (Pretty.output o pretty_def) def |> error)])
      end
  | add_check_transform (name, Classinst (clsname, (tyco, arity), memdefs)) =
      let
        fun check [Classmember (_, v, mtyp_c), Fun (_, (_, mtyp_i))] =
          let
            val mtyp_i' = instant_itype (v, tyco `%%
              map2 IVarT ((invent_var_t_names [mtyp_c] (length arity) [] "a"), arity)) mtyp_c;
          in if eq_itype (mtyp_i', mtyp_i) (*! PERHAPS TOO STRICT !*)
          then NONE
          else "wrong type signature for class member: "
            ^ (Pretty.output o pretty_itype) mtyp_i' ^ " expected,"
            ^ (Pretty.output o pretty_itype) mtyp_i ^ " given" |> SOME end
      in
        (map (fn (memname, memprim) => ((writeln memname; writeln memprim; [memname, memprim]), check)) memdefs,
          [(clsname,
              fn Class (supcs, mems, insts) => Class (supcs, mems, name::insts)
               | def => "attempted to add class instance to non-class"
                  ^ (Pretty.output o pretty_def) def |> error),
           (tyco,
              fn Datatype (vs, cs, clss) => Datatype (vs, cs, clsname::clss)
               | Nop => Nop
               | def => "attempted to instantiate non-type to class instance"
                  ^ (Pretty.output o pretty_def) def |> error)])
      end
  | add_check_transform _ = ([], []);

fun succeed some = (pair o Succeed) some;
fun fail msg = (pair o Fail) msg;

fun check_fail msg' (Succeed dst, trns) = (dst, trns)
  | check_fail msg' (Fail errmsg, _) = (tracing ("ROLLBACK CHECK: " ^ errmsg ^ "\n" ^ msg'); raise FAIL errmsg);

fun handle_fail msg f modl =
  f modl handle FAIL msg' => ([], modl) |> fail (msg ^ "\n" ^ msg');

fun select_generator print_msg src [] trns =
      fail ("no code generator available") trns
  | select_generator print_msg src [(gname, cgen)] trns =
      (print_msg gname; cgen src trns)
  | select_generator print_msg src ((gname, cgen)::cgens) trns =
      case cgen src trns
       of result as (Succeed _, _) =>
            (print_msg gname; result)
        | _ => select_generator print_msg src cgens trns

fun gen_invoke codegens msg src (deps, modl) =
  ([], modl)
  |> select_generator (fn gname => "choosing code generator " ^ gname ^ " for source " ^ quote msg)
       src codegens
  |> check_fail msg
  ||> (fn (deps', modl') => (append deps' deps, modl'));

fun gen_ensure_def defgens msg name (deps, modl) =
  let
    fun add (name, def) (deps, modl) =
      let
        val (checks, trans) = add_check_transform (name, def);
        fun check (check_defs, checker) modl =
          case checker (check_defs |> filter NameSpace.is_qualified |> map (get_def modl))
           of NONE => modl
            | SOME e => raise FAIL e;
        fun transform (name, f) modl =
          modl
          |> K (NameSpace.is_qualified name) ? map_def name f;
      in
        modl
        |> fold check checks
        |> fold (curry add_dep name) deps
        |> map_def name (fn _ => def)
        |> fold transform trans
      end;
    fun ensure_node name modl =
      if can (get_def modl) name
      then ([name], modl)
      else
        ([], modl |> add_def (name, Nop))
        |> select_generator (fn gname => "choosing code generator " ^ gname ^ " for definition of " ^ quote name)
             name defgens
        |> check_fail msg
        |-> (fn (def, names') =>
           add (name, def)
           #> fold_map ensure_node names')
        |-> (fn names' => pair (name :: Library.flat names'))
  in
    modl
    |> ensure_node name
    |-> (fn names => pair (names@deps))
  end;



(** primitive language constructs **)

val class_eq = "Eqtype"; (*defined for all primitve types and extensionally for all datatypes*)
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
val fun_primeq = "primeq"; (*defined for all primitive types*)
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

infix 7 xx;
infix 5 **;
infix 5 &&;

fun a xx b = Type_pair a b;
fun a ** b =
  let
    val ty_a = itype_of_iexpr a;
    val ty_b = itype_of_iexpr b;
  in IConst (cons_pair, ty_a `-> ty_b `-> ty_a xx ty_b) `$ a `$ b end;
fun a && b =
  let
    val ty_a = itype_of_ipat a;
    val ty_b = itype_of_ipat b;
  in ICons ((cons_pair, [a, b]), ty_a xx ty_b) end;

end; (* local *)

val prims = [class_eq, type_bool, type_integer, type_float, type_pair, type_list,
  cons_true, cons_false, cons_pair, cons_nil, cons_cons, fun_primeq, fun_eq, fun_not, fun_and,
  fun_or, fun_if, fun_fst, fun_snd, fun_add, fun_mult, fun_minus, fun_lt, fun_le, fun_wfrec];

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



(** generic transformation **)

fun eta_expand query =
  let
    fun eta_app ((f, ty), es) =
      let
        val delta = query f - length es;
        val add_n = if delta < 0 then 0 else delta;
        val add_vars =
          invent_var_e_names es add_n [] "x" ~~ Library.drop (length es, (fst o unfold_fun) ty);
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

fun connect_datatypes_clsdecls module =
  let
    fun extract_dep (name, Datatypecons (dtname, _)) = 
          [(dtname, name)]
      | extract_dep (name, Classmember (cls, _, _)) =
          [(cls, name)]
      | extract_dep (name, def) = []
  in add_deps extract_dep module end;

fun tupelize_cons module =
  let
    fun replace_def (_, (def as Datatypecons (_, []))) acc =
          (def, acc)
      | replace_def (_, (def as Datatypecons (_, [_]))) acc =
          (def, acc)
      | replace_def (name, (Datatypecons (tyco, tys))) acc =
          (Datatypecons (tyco,
            [foldl' (op xx) (NONE, tys)]), name::acc)
      | replace_def (_, def) acc = (def, acc);
    fun replace_app cs ((f, ty), es) =
      if member (op =) cs f
      then
        let
          val (tys, ty') = unfold_fun ty
        in IConst (f, foldr' (op xx) (tys, NONE) `-> ty') `$ foldl' (op **) (NONE, es) end
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
            ICons ((c, [(foldl' (op &&) (NONE, map (replace_ipat cs) ps))]), ty)
          else map_ipat I (replace_ipat cs) p
      | replace_ipat cs p = map_ipat I (replace_ipat cs) p;
  in
    transform_defs replace_def replace_ipat replace_iexpr [cons_cons] module
  end;

fun eliminate_dtconstr module =
  let
    fun replace_def (name, (Datatype (vs, cs, is))) acc =
          (Datatype (map (fn (v, _) => (v, [])) vs, cs, is), (name, vs)::acc)
      | replace_def (_, def) acc = (def, acc);
    fun constrain (ty as IType _, _) =
          ty
      | constrain (IVarT (v, sort1), (_, sort2)) =
          IVarT (v, gen_union (op =) (sort1, sort2));
    fun replace_ty tycos (ty as (IType (tyco, tys))) =
          (case AList.lookup (op =) tycos tyco
           of NONE => ty
            | SOME vs => IType (tyco, map2 constrain (tys, vs)))
      | replace_ty tycos ty =
          map_itype (replace_ty tycos) ty;
  in
    transform_defs replace_def
      (*! HIER FEHLT NOCH: ÄNDERN VON TYP UND SORTCTXT BEI FUNS !*)
      (fn tycos => map_ipat (replace_ty tycos) I)
      (fn tycos => map_iexpr (replace_ty tycos) (map_ipat (replace_ty tycos) I) I) [] module
  end;

fun eliminate_classes module =
  let
    fun mk_cls_typ_map memberdecls ty_inst =
      map (fn (memname, (v, ty)) =>
        (memname, ty |> instant_itype (v, ty_inst))) memberdecls;
    fun transform_dicts (Class (supcls, members, insts)) =
          let
            val memberdecls = AList.make
              ((fn Classmember (_, v, ty) => (v, ty)) o get_def module) members;
            val varname_cls = invent_var_t_names (map (snd o snd) memberdecls) 1 [] "a" |> hd;
          in
            Typesyn ([(varname_cls, [])], IDictT (mk_cls_typ_map memberdecls (IVarT (varname_cls, []))))
          end
      | transform_dicts (Classinst (tyco, (cls, arity), memdefs)) =
          let
            val Class (_, members, _) = get_def module cls;
            val memberdecls = AList.make
              ((fn Classmember (_, v, ty) => (v, ty)) o get_def module) members;
            val ty_arity = tyco `%% map IVarT (invent_var_t_names (map (snd o snd) memberdecls)
              (length arity) [] "a" ~~ arity);
            val inst_typ_map = mk_cls_typ_map memberdecls ty_arity;
            val memdefs_ty = map (fn (memname, memprim) =>
              (memname, (memprim, (the o AList.lookup (op =) inst_typ_map) memname))) memdefs;
          in
            Fun ([([], IDictE (map (apsnd IConst) memdefs_ty))],
              ([], IDictT inst_typ_map))
          end
      | transform_dicts d = d
    fun transform_defs (Fun (ds, (sortctxt, ty))) =
          let
            fun reduce f xs = foldl' f (NONE, xs);
            val varnames_ctxt =
              sortctxt
              |> length o Library.flat o map snd
              |> (fn used => invent_var_e_names (map snd ds) used ((vars_of_ipats o fst o hd) ds) "d")
              |> unflat (map snd sortctxt);
            val vname_alist = map2 (fn ((vt, sort), vs) => (vt, vs ~~ sort)) (sortctxt, varnames_ctxt);
            fun add_typarms ty =
              map (reduce (op xx) o (fn (vt, vss) => map (fn (_, cls) => cls `%% [IVarT (vt, [])]) vss)) vname_alist
                `--> ty;
            fun add_parms ps =
              map (reduce (op &&) o (fn (vt, vss) => map (fn (v, cls) => IVarP (v, cls `%% [IVarT (vt, [])])) vss)) vname_alist
                @ ps;
            fun transform_itype (IVarT (v, s)) =
                  IVarT (v, [])
              | transform_itype ty =
                  map_itype transform_itype ty;
            fun transform_ipat p =
                  map_ipat transform_itype transform_ipat p;
            fun transform_lookup (ClassPackage.Instance ((cdict, idict), ls)) = 
                  ls
                  |> transform_lookups
                  |-> (fn ty =>
                        curry mk_apps (IConst (idict, cdict `%% ty))
                        #> pair (cdict `%% ty))
              | transform_lookup (ClassPackage.Lookup (deriv, (v, i))) =
                  let
                    val (v', cls) =
                      (nth o the oo AList.lookup (op =)) vname_alist v i;
                    fun mk_parm tyco = tyco `%% [IVarT (v, [])];
                  in (mk_parm (hd (deriv)), ILookup (rev deriv, v')) end
            and transform_lookups lss =
                  map_yield (map_yield transform_lookup
                       #> apfst (reduce (op xx))
                       #> apsnd (reduce (op **))) lss;
            fun transform_iexpr (IInst (e, ls)) =
                  transform_iexpr e `$$ (snd o transform_lookups) ls
              | transform_iexpr e = 
                  map_iexpr transform_itype transform_ipat transform_iexpr e;
            fun transform_rhs (ps, rhs) = (add_parms ps, transform_iexpr rhs)
          in Fun (map transform_rhs ds, ([], add_typarms ty)) end
      | transform_defs d = d
  in
    module
    |> map_defs transform_dicts
    |> map_defs transform_defs
  end;

end; (* struct *)


structure CodegenThingol : CODEGEN_THINGOL =
struct

open CodegenThingolOp;

end; (* struct *)
