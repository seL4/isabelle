(* ========================================================================= *)
(* PRESERVING SHARING OF ML VALUES                                           *)
(* Copyright (c) 2005-2006 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

structure Sharing :> Sharing =
struct

infix ==

(* ------------------------------------------------------------------------- *)
(* Pointer equality.                                                         *)
(* ------------------------------------------------------------------------- *)

val pointerEqual = Portable.pointerEqual;

val op== = pointerEqual;

(* ------------------------------------------------------------------------- *)
(* List operations.                                                          *)
(* ------------------------------------------------------------------------- *)

fun map f =
    let
      fun m _ a_b [] = List.revAppend a_b
        | m ys a_b (x :: xs) =
          let
            val y = f x
            val ys = y :: ys
          in
            m ys (if x == y then a_b else (ys,xs)) xs
          end
    in
      fn l => m [] ([],l) l
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
