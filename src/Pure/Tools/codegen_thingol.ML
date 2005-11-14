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
    | IVarT of vname * sort;
  datatype ipat =
      ICons of (string * ipat list) * itype
    | IVarP of vname * itype;
  datatype iexpr =
      IConst of string * itype
    | IVarE of vname * itype
    | IApp of iexpr * iexpr
    | IInst of iexpr * ClassPackage.sortlookup list list
    | IAbs of (vname * itype) * iexpr
    | ICase of iexpr * (ipat * iexpr) list;
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
  val invent_tvar_names: itype list -> int -> vname list -> vname -> vname list;
  val invent_evar_names: iexpr list -> int -> vname list -> vname -> vname list;

  datatype def =
      Nop
    | Fun of (ipat list * iexpr) list * (ClassPackage.sortcontext * itype)
    | Typsyn of (vname * string list) list * itype
    | Datatyp of (vname * string list) list * string list * string list
    | Datatypcons of string * itype list
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
  val map_defs: (def -> def) -> module -> module;
  val add_deps: (string * def -> (string * string) list) -> module -> module;
  val fold_defs: (string * def -> 'a -> 'a) -> module -> 'a -> 'a;
  val fold_map_defs: (string * def -> 'a -> def * 'a) -> module -> 'a -> module * 'a;
  val merge_module: module * module -> module;
  val partof: string list -> module -> module;
  val succeed: 'a -> transact -> 'a transact_fin;
  val fail: string -> transact -> 'a transact_fin;
  val gen_invoke: (string * ('src, 'dst) gen_codegen) list -> string
    -> 'src -> transact -> 'dst * transact;
  val gen_ensure_def: (string * gen_defgen) list -> string
    -> string -> transact -> transact;

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
  | IVarT of vname * sort;

datatype ipat =
    ICons of (string * ipat list) * itype
  | IVarP of vname * itype;

datatype iexpr =
    IConst of string * itype
  | IVarE of vname * itype
  | IApp of iexpr * iexpr
  | IInst of iexpr * ClassPackage.sortlookup list list
  | IAbs of (vname * itype) * iexpr
  | ICase of iexpr * (ipat * iexpr) list;

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

fun invent_tvar_names tys n used a =
  let
    fun invent (IType (_, tys)) =
          fold invent tys
      | invent (IFun (ty1, ty2)) =
          invent ty1 #> invent ty2
      | invent (IVarT (v, _)) =
          cons v
in Term.invent_names (fold invent tys used) a n end;

fun invent_evar_names es n used a =
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
  | Typsyn of (vname * string list) list * itype
  | Datatyp of (vname * string list) list * string list * string list
  | Datatypcons of string * itype list
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
  | pretty_def (Typsyn (vs, ty)) =
      Pretty.block [
        Pretty.list "(" ")" (map (pretty_itype o IVarT) vs),
        Pretty.str " |=> ",
        pretty_itype ty
      ]
  | pretty_def (Datatyp (vs, cs, clss)) =
      Pretty.block [
        Pretty.list "(" ")" (map (pretty_itype o IVarT) vs),
        Pretty.str " |=> ",
        Pretty.gen_list " |" "" "" (map Pretty.str cs),
        Pretty.str ", instance of ",
        Pretty.gen_list "," "[" "]" (map Pretty.str clss)
      ]
  | pretty_def (Datatypcons (dtname, tys)) =
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
        fun mk_path ([], base) (PN (defs, modls)) =
              PN (base :: defs, modls)
          | mk_path (n::ns, base) (PN (defs, modls)) =
              modls
              |> AList.default (op =) (n, PN ([], []))
              |> AList.map_entry (op =) n (mk_path (ns, base))
              |> (pair defs #> PN);
        fun select (PN (defs, modls)) (Module module) =
          module
          |> Graph.subgraph (Graph.all_succs module (defs @ map fst modls))
          |> fold (fn (name, modls) => Graph.map_node name (select modls)) modls
          |> Module;
      in
        Module modl
        |> select (fold (mk_path o dest_name) (filter NameSpace.is_qualified names) (PN ([], [])))
        |> dest_modl
      end;

fun add_check_transform (name, (Datatypcons (dtname, _))) =
      ([([dtname],
          fn [Datatyp (_, _, [])] => NONE | _ => "attempted to add constructor to already instantiating datatype" |> SOME)],
       [(dtname,
          fn Datatyp (vs, cs, clss) => Datatyp (vs, name::cs, clss)
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
              map2 IVarT ((invent_tvar_names [mtyp_c] (length arity) [] "a"), arity)) mtyp_c;
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
              fn Datatyp (vs, cs, clss) => Datatyp (vs, cs, clsname::clss)
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

end; (* struct *)


structure CodegenThingol : CODEGEN_THINGOL =
struct

open CodegenThingolOp;

end; (* struct *)

