(* ========================================================================= *)
(* KNUTH-BENDIX TERM ORDERING CONSTRAINTS                                    *)
(* Copyright (c) 2002-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure KnuthBendixOrder :> KnuthBendixOrder =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun firstNotEqual f l =
    case List.find op<> l of
      SOME (x,y) => f x y
    | NONE => raise Bug "firstNotEqual";

(* ------------------------------------------------------------------------- *)
(* The weight of all constants must be at least 1, and there must be at most *)
(* one unary function with weight 0.                                         *)
(* ------------------------------------------------------------------------- *)

type kbo =
     {weight : Term.function -> int,
      precedence : Term.function * Term.function -> order};

(* Default weight = uniform *)

val uniformWeight : Term.function -> int = K 1;

(* Default precedence = by arity *)

val arityPrecedence : Term.function * Term.function -> order =
    fn ((f1,n1),(f2,n2)) =>
       case Int.compare (n1,n2) of
         LESS => LESS
       | EQUAL => String.compare (f1,f2)
       | GREATER => GREATER;

(* The default order *)

val default = {weight = uniformWeight, precedence = arityPrecedence};

(* ------------------------------------------------------------------------- *)
(* Term weight-1 represented as a linear function of the weight-1 of the     *)
(* variables in the term (plus a constant).                                  *)
(*                                                                           *)
(* Note that the conditions on weight functions ensure that all weights are  *)
(* at least 1, so all weight-1s are at least 0.                              *)
(* ------------------------------------------------------------------------- *)

datatype weight = Weight of int NameMap.map * int;

val weightEmpty : int NameMap.map = NameMap.new ();

val weightZero = Weight (weightEmpty,0);

fun weightIsZero (Weight (m,c)) = c = 0 andalso NameMap.null m;

fun weightNeg (Weight (m,c)) = Weight (NameMap.transform ~ m, ~c);

local
  fun add (n1,n2) =
      let
        val n = n1 + n2
      in
        if n = 0 then NONE else SOME n
      end;
in
  fun weightAdd (Weight (m1,c1)) (Weight (m2,c2)) =
      Weight (NameMap.union add m1 m2, c1 + c2);
end;

fun weightSubtract w1 w2 = weightAdd w1 (weightNeg w2);

fun weightMult 0 _ = weightZero
  | weightMult 1 w = w
  | weightMult k (Weight (m,c)) =
    let
      fun mult n = k * n
    in
      Weight (NameMap.transform mult m, k * c)
    end;

fun weightTerm weight =
    let
      fun wt m c [] = Weight (m,c)
        | wt m c (Term.Var v :: tms) =
          let
            val n = Option.getOpt (NameMap.peek m v, 0)
          in
            wt (NameMap.insert m (v, n + 1)) (c + 1) tms
          end
        | wt m c (Term.Fn (f,a) :: tms) =
          wt m (c + weight (f, length a)) (a @ tms)
    in
      fn tm => wt weightEmpty ~1 [tm]
    end;

fun weightIsVar v (Weight (m,c)) =
    c = 0 andalso NameMap.size m = 1 andalso NameMap.peek m v = SOME 1;

fun weightConst (Weight (_,c)) = c;

fun weightVars (Weight (m,_)) = 
    NameMap.foldl (fn (v,_,s) => NameSet.add s v) NameSet.empty m;

val weightsVars =
    List.foldl (fn (w,s) => NameSet.union (weightVars w) s) NameSet.empty;

fun weightVarList w = NameSet.toList (weightVars w);

fun weightNumVars (Weight (m,_)) = NameMap.size m;

fun weightNumVarsWithPositiveCoeff (Weight (m,_)) =
    NameMap.foldl (fn (_,n,z) => if n > 0 then z + 1 else z) 0 m;

fun weightCoeff var (Weight (m,_)) = Option.getOpt (NameMap.peek m var, 0);

fun weightCoeffs varList w = map (fn var => weightCoeff var w) varList;

fun weightCoeffSum (Weight (m,_)) = NameMap.foldl (fn (_,n,z) => n + z) 0 m;

fun weightLowerBound (w as Weight (m,c)) =
    if NameMap.exists (fn (_,n) => n < 0) m then NONE else SOME c;

fun weightNoLowerBound w = not (Option.isSome (weightLowerBound w));

fun weightAlwaysPositive w =
    case weightLowerBound w of NONE => false | SOME n => n > 0;

fun weightUpperBound (w as Weight (m,c)) =
    if NameMap.exists (fn (_,n) => n > 0) m then NONE else SOME c;

fun weightNoUpperBound w = not (Option.isSome (weightUpperBound w));

fun weightAlwaysNegative w =
    case weightUpperBound w of NONE => false | SOME n => n < 0;

fun weightGcd (w as Weight (m,c)) =
    NameMap.foldl (fn (_,i,k) => gcd i k) (Int.abs c) m;

fun ppWeightList pp =
    let
      fun coeffToString n =
          if n < 0 then "~" ^ coeffToString (~n)
          else if n = 1 then ""
          else Int.toString n

      fun pp_tm pp ("",n) = Parser.ppInt pp n
        | pp_tm pp (v,n) = Parser.ppString pp (coeffToString n ^ v)
    in
      fn [] => Parser.ppInt pp 0
       | tms => Parser.ppSequence " +" pp_tm pp tms
    end;

fun ppWeight pp (Weight (m,c)) =
    let
      val l = NameMap.toList m
      val l = if c = 0 then l else l @ [("",c)]
    in
      ppWeightList pp l
    end;

val weightToString = Parser.toString ppWeight;

(* ------------------------------------------------------------------------- *)
(* The Knuth-Bendix term order.                                              *)
(* ------------------------------------------------------------------------- *)

datatype kboOrder = Less | Equal | Greater | SignOf of weight;

fun kboOrder {weight,precedence} =
    let
      fun weightDifference tm1 tm2 =
          let
            val w1 = weightTerm weight tm1
            and w2 = weightTerm weight tm2
          in
            weightSubtract w2 w1
          end

      fun weightLess tm1 tm2 =
          let
            val w = weightDifference tm1 tm2
          in
            if weightIsZero w then precedenceLess tm1 tm2
            else weightDiffLess w tm1 tm2
          end

      and weightDiffLess w tm1 tm2 =
          case weightLowerBound w of
            NONE => false
          | SOME 0 => precedenceLess tm1 tm2
          | SOME n => n > 0

      and precedenceLess (Term.Fn (f1,a1)) (Term.Fn (f2,a2)) =
          (case precedence ((f1, length a1), (f2, length a2)) of
             LESS => true
           | EQUAL => firstNotEqual weightLess (zip a1 a2)
           | GREATER => false)
        | precedenceLess _ _ = false

      fun weightDiffGreater w tm1 tm2 = weightDiffLess (weightNeg w) tm2 tm1

      fun weightCmp tm1 tm2 =
          let
            val w = weightDifference tm1 tm2
          in
            if weightIsZero w then precedenceCmp tm1 tm2
            else if weightDiffLess w tm1 tm2 then Less
            else if weightDiffGreater w tm1 tm2 then Greater
            else SignOf w
          end

      and precedenceCmp (Term.Fn (f1,a1)) (Term.Fn (f2,a2)) =
          (case precedence ((f1, length a1), (f2, length a2)) of
             LESS => Less
           | EQUAL => firstNotEqual weightCmp (zip a1 a2)
           | GREATER => Greater)
        | precedenceCmp _ _ = raise Bug "kboOrder.precendenceCmp"
    in
      fn (tm1,tm2) => if tm1 = tm2 then Equal else weightCmp tm1 tm2
    end;

fun compare kbo tm1_tm2 =
    case kboOrder kbo tm1_tm2 of
      Less => SOME LESS
    | Equal => SOME EQUAL
    | Greater => SOME GREATER
    | SignOf _ => NONE;

(*TRACE7
val compare = fn kbo => fn (tm1,tm2) =>
    let
      val () = Parser.ppTrace Term.pp "KnuthBendixOrder.compare: tm1" tm1
      val () = Parser.ppTrace Term.pp "KnuthBendixOrder.compare: tm2" tm2
      val result = compare kbo (tm1,tm2)
      val () =
          case result of
            NONE => trace "KnuthBendixOrder.compare: result = Incomparable\n"
          | SOME x =>
            Parser.ppTrace Parser.ppOrder "KnuthBendixOrder.compare: result" x
    in
      result
    end;
*)

end
