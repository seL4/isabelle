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


(* auxiliary *)

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

end; (* struct *)


structure CodegenThingol : CODEGEN_THINGOL =
struct

infix 8 `%%;
infixr 6 `->;
infixr 6 `-->;
infix 4 `$;
infix 4 `$$;

open CodegenThingolOp;

end; (* struct *)

