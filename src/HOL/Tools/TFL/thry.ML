(*  Title:      HOL/Tools/TFL/thry.ML
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

local

fun tybind (ixn, (S, T)) = (TVar (ixn, S), T);

in

fun match_term thry pat ob =
  let
    val (ty_theta, tm_theta) = Pattern.match thry (pat,ob) (Vartab.empty, Vartab.empty);
    fun tmbind (ixn, (T, t)) = (Var (ixn, Envir.subst_type ty_theta T), t)
  in (map tmbind (Vartab.dest tm_theta), map tybind (Vartab.dest ty_theta))
  end;

fun match_type thry pat ob =
  map tybind (Vartab.dest (Sign.typ_match thry (pat, ob) Vartab.empty));

end;


(*---------------------------------------------------------------------------
 * Typing
 *---------------------------------------------------------------------------*)

fun typecheck thry t =
  Thm.cterm_of thry t
    handle TYPE (msg, _, _) => raise THRY_ERR "typecheck" msg
      | TERM (msg, _) => raise THRY_ERR "typecheck" msg;


(*---------------------------------------------------------------------------
 * Get information about datatypes
 *---------------------------------------------------------------------------*)

fun match_info thy dtco =
  case (Datatype.get_info thy dtco,
         Datatype.get_constrs thy dtco) of
      (SOME { case_name, ... }, SOME constructors) =>
        SOME {case_const = Const (case_name, Sign.the_const_type thy case_name), constructors = map Const constructors}
    | _ => NONE;

fun induct_info thy dtco = case Datatype.get_info thy dtco of
        NONE => NONE
      | SOME {nchotomy, ...} =>
          SOME {nchotomy = nchotomy,
                constructors = (map Const o the o Datatype.get_constrs thy) dtco};

fun extract_info thy =
 let val infos = (map snd o Symtab.dest o Datatype.get_all) thy
 in {case_congs = map (mk_meta_eq o #case_cong) infos,
     case_rewrites = List.concat (map (map mk_meta_eq o #case_rewrites) infos)}
 end;


end;
