(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      sys/eqrule_FOL_data.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    18 Feb 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Data for equality rules in the logic

*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
structure ZF_EqRuleData : EQRULE_DATA =
struct

fun mk_eq th = case concl_of th of
        Const("==",_)$_$_       => SOME (th)
    |   _$(Const("op <->",_)$_$_) => SOME (th RS iff_reflection)
    |   _$(Const("op =",_)$_$_) => SOME (th RS eq_reflection)
    |   _ => NONE;

val tranformation_pairs =
  [("op -->", [mp]), ("op &", [conjunct1,conjunct2]),
   ("All", [spec]), ("True", []), ("False", [])];

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
structure EqRuleData = ZF_EqRuleData;

structure EQSubstTac = 
  EQSubstTacFUN(structure EqRuleData = EqRuleData);
