(*  Title:      HOLCF/holcf_logic.ML
    ID:         $Id$
    Author:     David von Oheimb

Abstract syntax operations for HOLCF.
*)

infixr 6 ->>;

signature HOLCF_LOGIC =
sig
  val mk_btyp: string -> typ * typ -> typ
  val pcpoC: class
  val pcpoS: sort
  val mk_TFree: string -> typ
  val cfun_arrow: string
  val ->> : typ * typ -> typ
  val mk_ssumT: typ * typ -> typ
  val mk_sprodT: typ * typ -> typ
  val mk_uT: typ -> typ
  val trT: typ
  val oneT: typ
end;

structure HOLCFLogic: HOLCF_LOGIC =
struct

(* sort pcpo *)

val pcpoC = Sign.intern_class (the_context ()) "pcpo";
val pcpoS = [pcpoC];
fun mk_TFree s = TFree ("'" ^ s, pcpoS);


(* basic types *)

fun mk_btyp t (S,T) = Type (t,[S,T]);

local
  val intern_type = Sign.intern_type (the_context ());
  val u = intern_type "u";
in

val cfun_arrow = intern_type "->";
val op ->> = mk_btyp cfun_arrow;
val mk_ssumT = mk_btyp (intern_type "++");
val mk_sprodT = mk_btyp (intern_type "**");
fun mk_uT T = Type (u, [T]);
val trT = Type (intern_type "tr" , []);
val oneT = Type (intern_type "one", []);

end;

end;
