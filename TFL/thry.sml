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
    let val tsig = #tsig(Sign.rep_sg(sign_of thry))
        val (ty_theta,tm_theta) = Pattern.match tsig (pat,ob)
    in (map tmbind tm_theta, map tybind ty_theta)
    end

 fun match_type thry pat ob = 
    map tybind(Type.typ_match (#tsig(Sign.rep_sg(sign_of thry))) ([],(pat,ob)))
end;


(*---------------------------------------------------------------------------
 * Typing 
 *---------------------------------------------------------------------------*)

fun typecheck thry = cterm_of (sign_of thry);


(*---------------------------------------------------------------------------
 *     A collection of facts about datatypes
 *---------------------------------------------------------------------------*)
val nat_record = Dtype.build_record (Nat.thy, ("nat",["0","Suc"]), nat_ind_tac)
val prod_record =
    let val prod_case_thms = Dtype.case_thms (sign_of Prod.thy) [split] 
                                 (fn s => res_inst_tac [("p",s)] PairE_lemma)
         fun const s = Const(s, the(Sign.const_type (sign_of Prod.thy) s))
     in ("*", 
         {constructors = [const "Pair"],
            case_const = const "split",
         case_rewrites = [split RS eq_reflection],
             case_cong = #case_cong prod_case_thms,
              nchotomy = #nchotomy prod_case_thms}) 
     end;

(*---------------------------------------------------------------------------
 * Hacks to make interactive mode work. Referring to "datatypes" directly
 * is temporary, I hope!
 *---------------------------------------------------------------------------*)
val match_info = fn thy =>
    fn "*" => Some({case_const = #case_const (#2 prod_record),
                     constructors = #constructors (#2 prod_record)})
     | "nat" => Some({case_const = #case_const (#2 nat_record),
                       constructors = #constructors (#2 nat_record)})
     | ty => case assoc(!datatypes,ty)
               of None => None
                | Some{case_const,constructors, ...} =>
                   Some{case_const=case_const, constructors=constructors}

val induct_info = fn thy =>
    fn "*" => Some({nchotomy = #nchotomy (#2 prod_record),
                     constructors = #constructors (#2 prod_record)})
     | "nat" => Some({nchotomy = #nchotomy (#2 nat_record),
                       constructors = #constructors (#2 nat_record)})
     | ty => case assoc(!datatypes,ty)
               of None => None
                | Some{nchotomy,constructors, ...} =>
                  Some{nchotomy=nchotomy, constructors=constructors}

val extract_info = fn thy => 
 let val case_congs = map (#case_cong o #2) (!datatypes)
         val case_rewrites = flat(map (#case_rewrites o #2) (!datatypes))
 in {case_congs = #case_cong (#2 prod_record)::
                  #case_cong (#2 nat_record)::case_congs,
     case_rewrites = #case_rewrites(#2 prod_record)@
                     #case_rewrites(#2 nat_record)@case_rewrites}
 end;

end; (* Thry *)
