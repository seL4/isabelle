(*  Title:      TFL/thry.ML
    ID:         $Id$
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge
*)

signature THRY =
sig
  val match_term: theory -> term -> term -> (term * term) list * (typ * typ) list
  val match_type: theory -> typ -> typ -> (typ * typ) list
  val typecheck: theory -> term -> cterm
  (*datatype facts of various flavours*)
  val match_info: theory -> string -> {constructors: term list, case_const: term} option
  val induct_info: theory -> string -> {constructors: term list, nchotomy: thm} option
  val extract_info: theory -> {case_congs: thm list, case_rewrites: thm list}
end;

structure Thry: THRY =
struct


fun THRY_ERR func mesg = Utils.ERR {module = "Thry", func = func, mesg = mesg};


(*---------------------------------------------------------------------------
 *    Matching
 *---------------------------------------------------------------------------*)

local fun tybind (x,y) = (TVar (x, HOLogic.typeS) , y)
      fun tmbind (x,y) = (Var  (x, Term.type_of y), y)
in
 fun match_term thry pat ob =
    let val tsig = Sign.tsig_of (Theory.sign_of thry)
        val (ty_theta,tm_theta) = Pattern.match tsig (pat,ob)
    in (map tmbind tm_theta, map tybind ty_theta)
    end

 fun match_type thry pat ob = map tybind (Vartab.dest
   (Type.typ_match (Sign.tsig_of (Theory.sign_of thry)) (Vartab.empty, (pat,ob))))
end;


(*---------------------------------------------------------------------------
 * Typing
 *---------------------------------------------------------------------------*)

fun typecheck thry t =
  Thm.cterm_of (Theory.sign_of thry) t
    handle TYPE (msg, _, _) => raise THRY_ERR "typecheck" msg
      | TERM (msg, _) => raise THRY_ERR "typecheck" msg;


(*---------------------------------------------------------------------------
 * Get information about datatypes
 *---------------------------------------------------------------------------*)

fun get_info thy ty = Symtab.lookup (DatatypePackage.get_datatypes thy, ty);

fun match_info thy tname =
  case (DatatypePackage.case_const_of thy tname, DatatypePackage.constrs_of thy tname) of
      (Some case_const, Some constructors) =>
        Some {case_const = case_const, constructors = constructors}
    | _ => None;

fun induct_info thy tname = case get_info thy tname of
        None => None
      | Some {nchotomy, ...} =>
          Some {nchotomy = nchotomy,
                constructors = the (DatatypePackage.constrs_of thy tname)};

fun extract_info thy =
 let val infos = map snd (Symtab.dest (DatatypePackage.get_datatypes thy))
 in {case_congs = map (mk_meta_eq o #case_cong) infos,
     case_rewrites = flat (map (map mk_meta_eq o #case_rewrites) infos)}
 end;


end;
