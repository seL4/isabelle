(*  Title:      TFL/thry
    ID:         $Id$
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge
*)

structure Thry : Thry_sig (* LThry_sig *) = 
struct

structure S = USyntax;

fun THRY_ERR{func,mesg} = Utils.ERR{module = "Thry",func=func,mesg=mesg};

(*---------------------------------------------------------------------------
 *    Matching 
 *---------------------------------------------------------------------------*)

local fun tybind (x,y) = (TVar (x,["term"]) , y)
      fun tmbind (x,y) = (Var  (x,type_of y), y)
in
 fun match_term thry pat ob = 
    let val tsig = #tsig(Sign.rep_sg(Theory.sign_of thry))
        val (ty_theta,tm_theta) = Pattern.match tsig (pat,ob)
    in (map tmbind tm_theta, map tybind ty_theta)
    end

 fun match_type thry pat ob = map tybind (Vartab.dest
   (Type.typ_match (#tsig(Sign.rep_sg(Theory.sign_of thry))) (Vartab.empty, (pat,ob))))
end;


(*---------------------------------------------------------------------------
 * Typing 
 *---------------------------------------------------------------------------*)

fun typecheck thry = Thm.cterm_of (Theory.sign_of thry);


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

end; (* Thry *)
