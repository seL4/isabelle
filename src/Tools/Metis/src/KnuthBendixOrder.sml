(* ========================================================================= *)
(* KNUTH-BENDIX TERM ORDERING CONSTRAINTS                                    *)
(* Copyright (c) 2002 Joe Leslie-Hurd, distributed under the BSD License     *)
(* ========================================================================= *)

structure KnuthBendixOrder :> KnuthBendixOrder =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun notEqualTerm (x,y) = not (Term.equal x y);

fun firstNotEqualTerm f l =
    case List.find notEqualTerm l of
      SOME (x,y) => f x y
    | NONE => raise Bug "firstNotEqualTerm";

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
       | EQUAL => Name.compare (f1,f2)
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
  fun add ((_,n1),(_,n2)) =
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

(* ------------------------------------------------------------------------- *)
(* 2026-09-18: Martin Desharnais-Schaefer proposed optimizing weightTerm as  *)
(* below to reduce the amount of memory allocation by Metis in Isabelle:     *)
(*                                                                           *)
(* "This was based on a test of 2180 problems handed from Isabelle to        *)
(* Resolution.new, exported with Tptp.write and replayed under Poly/ML's     *)
(* allocation profiler, one process per problem, 60s limit. The optimized    *)
(* version uses 15.3% less memory allocation than the reference version. For *)
(* scale, weightTerm is 1.8–2.2% of Metis's total allocation on this corpus, *)
(* against 6.8% for the single largest consumer: Literal.subst."             *)
(* ------------------------------------------------------------------------- *)

fun weightTerm weight =
    let
      fun incrementVar m v =
          let
            val n = Option.getOpt (NameMap.peek m v, 0)
          in
            NameMap.insert m (v, n + 1)
          end

      fun wt m c (Term.Var v) tms1 tms2 pending =
          next (incrementVar m v) (c + 1) tms1 tms2 pending
        | wt m c (Term.Fn (f,a)) tms1 tms2 pending =
          let
            val c = c + weight (f, length a)
          in
            case a of
              [] => next m c tms1 tms2 pending
            | [tm] => wt m c tm tms1 tms2 pending
            | [Term.Var v, tm] => wt (incrementVar m v) (c + 1) tm tms1 tms2 pending
            | [tm, Term.Var v] => wt (incrementVar m v) (c + 1) tm tms1 tms2 pending
            | [Term.Fn (g,[]), tm] => wt m (c + weight (g,0)) tm tms1 tms2 pending
            | [tm, Term.Fn (g,[])] => wt m (c + weight (g,0)) tm tms1 tms2 pending
            | tm :: args =>
              if List.null tms1 then
                wt m c tm args tms2 pending
              else if List.null tms2 then
                wt m c tm args tms1 pending
              else
                wt m c tm args tms1 (tms2 :: pending)
          end

      and next m c (tm :: tms1) tms2 pending = wt m c tm tms1 tms2 pending
        | next m c [] (tm :: tms2) pending = wt m c tm tms2 [] pending
        | next m c [] [] (tms1 :: pending) = next m c tms1 [] pending
        | next m c [] [] [] = Weight (m,c)
    in
      fn tm => wt weightEmpty ~1 tm [] [] []
    end;

(*MetisDebug
fun weightTermRef weight =
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

val weightTerm = fn weight => fn tm =>
    let
      val w1 = weightTerm weight tm
      val w2 = weightTermRef weight tm
    in
      if weightIsZero (weightSubtract w1 w2) then w1
      else raise Useful.Bug "KnuthBendixOrdering.weightTerm: doesn't match reference"
    end;
*)

fun weightLowerBound (w as Weight (m,c)) =
    if NameMap.exists (fn (_,n) => n < 0) m then NONE else SOME c;

(*MetisDebug
val ppWeightList =
    let
      fun ppCoeff n =
          if n < 0 then Print.sequence (Print.ppString "~") (ppCoeff (~n))
          else if n = 1 then Print.skip
          else Print.ppInt n

      fun pp_tm (NONE,n) = Print.ppInt n
        | pp_tm (SOME v, n) = Print.sequence (ppCoeff n) (Name.pp v)
    in
      fn [] => Print.ppInt 0
       | tms => Print.ppOpList " +" pp_tm tms
    end;

fun ppWeight (Weight (m,c)) =
    let
      val l = NameMap.toList m
      val l = List.map (fn (v,n) => (SOME v, n)) l
      val l = if c = 0 then l else l @ [(NONE,c)]
    in
      ppWeightList l
    end;

val weightToString = Print.toString ppWeight;
*)

(* ------------------------------------------------------------------------- *)
(* The Knuth-Bendix term order.                                              *)
(* ------------------------------------------------------------------------- *)

fun compare {weight,precedence} =
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
           | EQUAL => firstNotEqualTerm weightLess (zip a1 a2)
           | GREATER => false)
        | precedenceLess _ _ = false

      fun weightDiffGreater w tm1 tm2 = weightDiffLess (weightNeg w) tm2 tm1

      fun weightCmp tm1 tm2 =
          let
            val w = weightDifference tm1 tm2
          in
            if weightIsZero w then precedenceCmp tm1 tm2
            else if weightDiffLess w tm1 tm2 then SOME LESS
            else if weightDiffGreater w tm1 tm2 then SOME GREATER
            else NONE
          end

      and precedenceCmp (Term.Fn (f1,a1)) (Term.Fn (f2,a2)) =
          (case precedence ((f1, length a1), (f2, length a2)) of
             LESS => SOME LESS
           | EQUAL => firstNotEqualTerm weightCmp (zip a1 a2)
           | GREATER => SOME GREATER)
        | precedenceCmp _ _ = raise Bug "kboOrder.precendenceCmp"
    in
      fn (tm1,tm2) =>
         if Term.equal tm1 tm2 then SOME EQUAL else weightCmp tm1 tm2
    end;

(*MetisTrace7
val compare = fn kbo => fn (tm1,tm2) =>
    let
      val () = Print.trace Term.pp "KnuthBendixOrder.compare: tm1" tm1
      val () = Print.trace Term.pp "KnuthBendixOrder.compare: tm2" tm2
      val result = compare kbo (tm1,tm2)
      val () =
          case result of
            NONE => trace "KnuthBendixOrder.compare: result = Incomparable\n"
          | SOME x =>
            Print.trace Print.ppOrder "KnuthBendixOrder.compare: result" x
    in
      result
    end;
*)

end
