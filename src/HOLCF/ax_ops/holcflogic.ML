(*
    ID:         $Id$
    Author:     Tobias Mayr

Additional term and type constructors, extension of Pure/term.ML, logic.ML
and HOL/hologic.ML

TODO:

*)

signature HOLCFLOGIC =
sig
 val True  : term;
 val False : term;
 val Imp   : term;
 val And   : term;
 val Not   : term;
 val mkNot : term -> term;                (* negates, no Trueprop *)
 val mkNotEqUU : term -> term;            (* Trueprop(x ~= UU) *)
 val mkNotEqUU_in : term -> term -> term; (* "v~=UU ==> t" *)
 val ==>     : typ * typ -> typ;          (* Infix operation typ constructor *)
 val cfun_arrow : string                  (* internalized "->" *)
 val mkOpApp : term -> term -> term;      (* Ops application (f ` x) *)
 val mkCPair : term -> term -> term;      (* cpair constructor *)
end;

structure HOLCFlogic : HOLCFLOGIC =
struct
open Logic 
open HOLogic

val True = Const("True",boolT);
val False = Const("False",boolT);
val Imp = Const("op -->",boolT --> boolT --> boolT);
val And = Const("op &",boolT --> boolT --> boolT);
val Not = Const("Not",boolT --> boolT);   

fun mkNot A = Not $ A; (* negates, no Trueprop *)

(* Trueprop(x ~= UU) *)
fun mkNotEqUU v = mk_Trueprop(mkNot(mk_eq(v,Const("UU",fastype_of v))));

(* mkNotEqUU_in v t = "v~=UU ==> t" *)
fun mkNotEqUU_in vterm term = 
   mk_implies(mkNotEqUU vterm,term)

val HOLCF_sg = sign_of HOLCF.thy;
fun mk_typ t (S,T) = Sign.intern_typ HOLCF_sg (Type(t,[S,T]));
fun rep_Type  (Type  x) = x| rep_Type _ = error "Internal error: rep_Type";

infixr 6 ==>; (* the analogon to --> for operations *)
val op ==> = mk_typ "->";
val cfun_arrow = fst (rep_Type (dummyT ==> dummyT));

(* Ops application (f ` x) *)
fun mkOpApp (f as Const(_,ft as Type(_(*"->"*),[xt,rt]))) x =
     Const("fapp",ft --> xt --> rt) $ f $ x
  | mkOpApp f x = (error("Internal error: mkOpApp: wrong args"));

(* cpair constructor *)
fun mkCPair x y = let val tx = fastype_of x
                       val ty = fastype_of y
                   in  
      Const("fapp",(ty==>Type("*",[tx,ty]))-->ty-->Type("*",[tx,ty])) $
      (mkOpApp (Const("cpair",tx ==> ty ==> Type("*",[tx,ty]))) x) $ y
                   end;

end;
