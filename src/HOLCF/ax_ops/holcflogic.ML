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
val Not = Const("not",boolT --> boolT);   

fun mkNot A = Not $ A; (* negates, no Trueprop *)

(* Trueprop(x ~= UU) *)
fun mkNotEqUU v = mk_Trueprop(mkNot(mk_eq(v,Const("UU",fastype_of v))));

(* mkNotEqUU_in v t = "v~=UU ==> t" *)
fun mkNotEqUU_in vterm term = 
   mk_implies(mkNotEqUU vterm,term)


infixr 6 ==>; (* the analogon to --> for operations *)
fun a ==> b = Type("->",[a,b]);

(* Ops application (f ` x) *)
fun mkOpApp (f as Const(_,ft as Type("->",[xt,rt]))) x =
     Const("fapp",ft --> xt --> rt) $ f $ x
  | mkOpApp f x = (print(f);error("Internal error: mkOpApp: wrong args"));

(* cpair constructor *)
fun mkCPair x y = let val tx = fastype_of x
                       val ty = fastype_of y
                   in  
      Const("fapp",(ty==>Type("*",[tx,ty]))-->ty-->Type("*",[tx,ty])) $
      (mkOpApp (Const("cpair",tx ==> ty ==> Type("*",[tx,ty]))) x) $ y
                   end;

end;
