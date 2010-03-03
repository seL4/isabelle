(*  Title:      HOLCF/holcf_logic.ML
    Author:     David von Oheimb

Abstract syntax operations for HOLCF.
*)

infixr 6 ->>;

signature HOLCF_LOGIC =
sig
  val mk_btyp: string -> typ * typ -> typ
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

val pcpoS = @{sort pcpo};
fun mk_TFree s = TFree ("'" ^ s, pcpoS);


(* basic types *)

fun mk_btyp t (S, T) = Type (t, [S, T]);

val cfun_arrow = @{type_name "cfun"};
val op ->> = mk_btyp cfun_arrow;
val mk_ssumT = mk_btyp (@{type_name "ssum"});
val mk_sprodT = mk_btyp (@{type_name "sprod"});
fun mk_uT T = Type (@{type_name u}, [T]);
val trT = @{typ tr};
val oneT = @{typ one};

end;
