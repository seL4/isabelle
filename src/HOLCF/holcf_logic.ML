(*  Title:      HOLCF/holcf_logic.ML
    ID:         $Id$
    Author:     David von Oheimb

Abstract syntax operations for HOLCF.
*)

infixr 6 ->>;

signature HOLCF_LOGIC =
sig
  val mk_btyp: string -> typ * typ -> typ
  val mk_prodT:          typ * typ -> typ
  val mk_not:  term -> term

  val HOLCF_sg: Sign.sg
  val pcpoC: class
  val pcpoS: sort
  val mk_TFree: string -> typ
  val cfun_arrow: string
  val ->>      : typ * typ -> typ
  val mk_ssumT : typ * typ -> typ
  val mk_sprodT: typ * typ -> typ
  val mk_uT: typ -> typ
  val trT: typ
  val oneT: typ

end;


structure HOLCFLogic: HOLCF_LOGIC =
struct

local

  open HOLogic;

in

fun mk_btyp t (S,T) = Type (t,[S,T]);
val mk_prodT = mk_btyp "*";

fun mk_not P  = Const ("Not", boolT --> boolT) $ P;

(* basics *)

val HOLCF_sg    = sign_of HOLCF.thy;
val pcpoC       = Sign.intern_class HOLCF_sg "pcpo";
val pcpoS       = [pcpoC];
fun mk_TFree s  = TFree ("'"^s, pcpoS);

(*cfun, ssum, sprod, u, tr, one *)

local val intern = Sign.intern_tycon HOLCF_sg;
in
val cfun_arrow = intern "->";
val op   ->>  = mk_btyp cfun_arrow;
val mk_ssumT  = mk_btyp (intern "++");
val mk_sprodT = mk_btyp (intern "**");
fun mk_uT T   = Type (intern "u"  ,[T]);
val trT       = Type (intern "tr" ,[ ]);
val oneT      = Type (intern "one",[ ]);
end;

end; (* local *)
end; (* struct *)
