(* ========================================================================= *)
(* A LOGICAL KERNEL FOR FIRST ORDER CLAUSAL THEOREMS                         *)
(* Copyright (c) 2001 Joe Hurd, distributed under the BSD License            *)
(* ========================================================================= *)

structure Thm :> Thm =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* An abstract type of first order logic theorems.                           *)
(* ------------------------------------------------------------------------- *)

type clause = LiteralSet.set;

datatype inferenceType =
    Axiom
  | Assume
  | Subst
  | Factor
  | Resolve
  | Refl
  | Equality;

datatype thm = Thm of clause * (inferenceType * thm list);

type inference = inferenceType * thm list;

(* ------------------------------------------------------------------------- *)
(* Theorem destructors.                                                      *)
(* ------------------------------------------------------------------------- *)

fun clause (Thm (cl,_)) = cl;

fun inference (Thm (_,inf)) = inf;

(* Tautologies *)

local
  fun chk (_,NONE) = NONE
    | chk ((pol,atm), SOME set) =
      if (pol andalso Atom.isRefl atm) orelse AtomSet.member atm set then NONE
      else SOME (AtomSet.add set atm);
in
  fun isTautology th =
      case LiteralSet.foldl chk (SOME AtomSet.empty) (clause th) of
        SOME _ => false
      | NONE => true;
end;

(* Contradictions *)

fun isContradiction th = LiteralSet.null (clause th);

(* Unit theorems *)

fun destUnit (Thm (cl,_)) =
    if LiteralSet.size cl = 1 then LiteralSet.pick cl
    else raise Error "Thm.destUnit";

val isUnit = can destUnit;

(* Unit equality theorems *)

fun destUnitEq th = Literal.destEq (destUnit th);

val isUnitEq = can destUnitEq;

(* Literals *)

fun member lit (Thm (cl,_)) = LiteralSet.member lit cl;

fun negateMember lit (Thm (cl,_)) = LiteralSet.negateMember lit cl;

(* ------------------------------------------------------------------------- *)
(* A total order.                                                            *)
(* ------------------------------------------------------------------------- *)

fun compare (th1,th2) = LiteralSet.compare (clause th1, clause th2);

fun equal th1 th2 = LiteralSet.equal (clause th1) (clause th2);

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

fun freeIn v (Thm (cl,_)) = LiteralSet.freeIn v cl;

fun freeVars (Thm (cl,_)) = LiteralSet.freeVars cl;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

fun inferenceTypeToString Axiom = "Axiom"
  | inferenceTypeToString Assume = "Assume"
  | inferenceTypeToString Subst = "Subst"
  | inferenceTypeToString Factor = "Factor"
  | inferenceTypeToString Resolve = "Resolve"
  | inferenceTypeToString Refl = "Refl"
  | inferenceTypeToString Equality = "Equality";

fun ppInferenceType inf =
    Print.ppString (inferenceTypeToString inf);

local
  fun toFormula th =
      Formula.listMkDisj
        (List.map Literal.toFormula (LiteralSet.toList (clause th)));
in
  fun pp th =
      Print.inconsistentBlock 3
        [Print.ppString "|- ",
         Formula.pp (toFormula th)];
end;

val toString = Print.toString pp;

(* ------------------------------------------------------------------------- *)
(* Primitive rules of inference.                                             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ----- axiom C                                                             *)
(*   C                                                                       *)
(* ------------------------------------------------------------------------- *)

fun axiom cl = Thm (cl,(Axiom,[]));

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ----------- assume L                                                      *)
(*   L \/ ~L                                                                 *)
(* ------------------------------------------------------------------------- *)

fun assume lit =
    Thm (LiteralSet.fromList [lit, Literal.negate lit], (Assume,[]));

(* ------------------------------------------------------------------------- *)
(*    C                                                                      *)
(* -------- subst s                                                          *)
(*   C[s]                                                                    *)
(* ------------------------------------------------------------------------- *)

fun subst sub (th as Thm (cl,inf)) =
    let
      val cl' = LiteralSet.subst sub cl
    in
      if Portable.pointerEqual (cl,cl') then th
      else
        case inf of
          (Subst,_) => Thm (cl',inf)
        | _ => Thm (cl',(Subst,[th]))
    end;

(* ------------------------------------------------------------------------- *)
(*   L \/ C    ~L \/ D                                                       *)
(* --------------------- resolve L                                           *)
(*        C \/ D                                                             *)
(*                                                                           *)
(* The literal L must occur in the first theorem, and the literal ~L must    *)
(* occur in the second theorem.                                              *)
(* ------------------------------------------------------------------------- *)

fun resolve lit (th1 as Thm (cl1,_)) (th2 as Thm (cl2,_)) =
    let
      val cl1' = LiteralSet.delete cl1 lit
      and cl2' = LiteralSet.delete cl2 (Literal.negate lit)
    in
      Thm (LiteralSet.union cl1' cl2', (Resolve,[th1,th2]))
    end;

(*MetisDebug
val resolve = fn lit => fn pos => fn neg =>
    resolve lit pos neg
    handle Error err =>
      raise Error ("Thm.resolve:\nlit = " ^ Literal.toString lit ^
                   "\npos = " ^ toString pos ^
                   "\nneg = " ^ toString neg ^ "\n" ^ err);
*)

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------- refl t                                                          *)
(*   t = t                                                                   *)
(* ------------------------------------------------------------------------- *)

fun refl tm = Thm (LiteralSet.singleton (true, Atom.mkRefl tm), (Refl,[]));

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------ equality L p t                                   *)
(*   ~(s = t) \/ ~L \/ L'                                                    *)
(*                                                                           *)
(* where s is the subterm of L at path p, and L' is L with the subterm at    *)
(* path p being replaced by t.                                               *)
(* ------------------------------------------------------------------------- *)

fun equality lit path t =
    let
      val s = Literal.subterm lit path

      val lit' = Literal.replace lit (path,t)

      val eqLit = Literal.mkNeq (s,t)

      val cl = LiteralSet.fromList [eqLit, Literal.negate lit, lit']
    in
      Thm (cl,(Equality,[]))
    end;

end
