(* ========================================================================= *)
(* PRESERVING SHARING OF ML VALUES                                           *)
(* Copyright (c) 2005-2006 Joe Hurd, distributed under the BSD License       *)
(* ========================================================================= *)

structure Sharing :> Sharing =
struct

infix ==

val op== = Portable.pointerEqual;

(* ------------------------------------------------------------------------- *)
(* Option operations.                                                        *)
(* ------------------------------------------------------------------------- *)

fun mapOption f xo =
    case xo of
      SOME x =>
      let
        val y = f x
      in
        if x == y then xo else SOME y
      end
    | NONE => xo;

fun mapsOption f xo acc =
    case xo of
      SOME x =>
      let
        val (y,acc) = f x acc
      in
        if x == y then (xo,acc) else (SOME y, acc)
      end
    | NONE => (xo,acc);

(* ------------------------------------------------------------------------- *)
(* List operations.                                                          *)
(* ------------------------------------------------------------------------- *)

fun map f =
    let
      fun m ys ys_xs xs =
          case xs of
            [] => List.revAppend ys_xs
          | x :: xs =>
            let
              val y = f x
              val ys = y :: ys
              val ys_xs = if x == y then ys_xs else (ys,xs)
            in
              m ys ys_xs xs
            end
    in
      fn xs => m [] ([],xs) xs
    end;

fun maps f =
    let
      fun m acc ys ys_xs xs =
          case xs of
            [] => (List.revAppend ys_xs, acc)
          | x :: xs =>
            let
              val (y,acc) = f x acc
              val ys = y :: ys
              val ys_xs = if x == y then ys_xs else (ys,xs)
            in
              m acc ys ys_xs xs
            end
    in
      fn xs => fn acc => m acc [] ([],xs) xs
    end;

local
  fun revTails acc xs =
      case xs of
        [] => acc
      | x :: xs' => revTails ((x,xs) :: acc) xs';
in
  fun revMap f =
      let
        fun m ys same xxss =
            case xxss of
              [] => ys
            | (x,xs) :: xxss =>
              let
                val y = f x
                val same = same andalso x == y
                val ys = if same then xs else y :: ys
              in
                m ys same xxss
              end
      in
        fn xs => m [] true (revTails [] xs)
      end;

  fun revMaps f =
      let
        fun m acc ys same xxss =
            case xxss of
              [] => (ys,acc)
            | (x,xs) :: xxss =>
              let
                val (y,acc) = f x acc
                val same = same andalso x == y
                val ys = if same then xs else y :: ys
              in
                m acc ys same xxss
              end
      in
        fn xs => fn acc => m acc [] true (revTails [] xs)
      end;
end;

fun updateNth (n,x) l =
    let
      val (a,b) = Useful.revDivide l n
    in
      case b of
        [] => raise Subscript
      | h :: t => if x == h then l else List.revAppend (a, x :: t)
    end;

fun setify l =
    let
      val l' = Useful.setify l
    in
      if length l' = length l then l else l'
    end;

(* ------------------------------------------------------------------------- *)
(* Function caching.                                                         *)
(* ------------------------------------------------------------------------- *)

fun cache cmp f =
    let
      val cache = ref (Map.new cmp)
    in
      fn a =>
         case Map.peek (!cache) a of
           SOME b => b
         | NONE =>
           let
             val b = f a
             val () = cache := Map.insert (!cache) (a,b)
           in
             b
           end
    end;

(* ------------------------------------------------------------------------- *)
(* Hash consing.                                                             *)
(* ------------------------------------------------------------------------- *)

fun hashCons cmp = cache cmp Useful.I;

end
