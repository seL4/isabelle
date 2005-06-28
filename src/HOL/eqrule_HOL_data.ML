(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      HOL/eqrule_HOL_data.ML
    Id:		$Id$
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Modified:   22 July 2004
    Created:    18 Feb 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Data for equality rules in the logic

*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
structure HOL_EqRuleData : EQRULE_DATA =
struct

val eq_reflection = thm "eq_reflection";
val mp = thm "mp";
val spec = thm "spec";
val if_bool_eq_conj = thm "if_bool_eq_conj";
val iffD1 = thm "iffD1";
val conjunct2 = thm "conjunct2";
val conjunct1 = thm "conjunct1";

fun mk_eq th = case concl_of th of
        Const("==",_)$_$_       => SOME (th)
    |   _$(Const("op =",_)$_$_) => SOME (th RS eq_reflection)
    |   _ => NONE;

val tranformation_pairs =
  [("op -->", [mp]), ("op &", [conjunct1,conjunct2]),
   ("All", [spec]), ("True", []), ("False", []),
   ("HOL.If", [if_bool_eq_conj RS iffD1])];

(*
val mk_atomize:      (string * thm list) list -> thm -> thm list
looks too specific to move it somewhere else
*)
fun mk_atomize pairs =
  let fun atoms th =
        (case Thm.concl_of th of
           Const("Trueprop",_) $ p =>
             (case Term.head_of p of
                Const(a,_) =>
                  (case Library.assoc(pairs,a) of
                     SOME(rls) => List.concat (map atoms ([th] RL rls))
                   | NONE => [th])
              | _ => [th])
         | _ => [th])
  in atoms end;

val prep_meta_eq = 
    (List.mapPartial  
       mk_eq
       o (mk_atomize tranformation_pairs)
       o Drule.gen_all 
       o zero_var_indexes)

end;

structure EqRuleData = HOL_EqRuleData;

structure EQSubstTac = 
  EQSubstTacFUN(structure EqRuleData = EqRuleData);


