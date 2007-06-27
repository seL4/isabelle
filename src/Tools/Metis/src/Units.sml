(* ========================================================================= *)
(* A STORE FOR UNIT THEOREMS                                                 *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Units :> Units =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* A type of unit store.                                                     *)
(* ------------------------------------------------------------------------- *)

type unitThm = Literal.literal * Thm.thm;

datatype units = Units of unitThm LiteralNet.literalNet;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val empty = Units (LiteralNet.new {fifo = false});

fun size (Units net) = LiteralNet.size net;

fun toString units = "U{" ^ Int.toString (size units) ^ "}";

val pp = Parser.ppMap toString Parser.ppString;

(* ------------------------------------------------------------------------- *)
(* Add units into the store.                                                 *)
(* ------------------------------------------------------------------------- *)

fun add (units as Units net) (uTh as (lit,th)) =
    let
      val net = LiteralNet.insert net (lit,uTh)
    in
      case total Literal.sym lit of
        NONE => Units net
      | SOME (lit' as (pol,_)) =>
        let
          val th' = (if pol then Rule.symEq else Rule.symNeq) lit th
          val net = LiteralNet.insert net (lit',(lit',th'))
        in
          Units net
        end
    end;

val addList = foldl (fn (th,u) => add u th);

(* ------------------------------------------------------------------------- *)
(* Matching.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun match (Units net) lit =
    let
      fun check (uTh as (lit',_)) =
          case total (Literal.match Subst.empty lit') lit of
            NONE => NONE
          | SOME sub => SOME (uTh,sub)
    in
      first check (LiteralNet.match net lit)
    end;

(* ------------------------------------------------------------------------- *)
(* Reducing by repeated matching and resolution.                             *)
(* ------------------------------------------------------------------------- *)

fun reduce units =
    let
      fun red1 (lit,news_th) =
          case total Literal.destIrrefl lit of
            SOME tm =>
            let
              val (news,th) = news_th
              val th = Thm.resolve lit th (Thm.refl tm)
            in
              (news,th)
            end
          | NONE =>
            let
              val lit' = Literal.negate lit
            in
              case match units lit' of
                NONE => news_th
              | SOME ((_,rth),sub) =>
                let
                  val (news,th) = news_th
                  val rth = Thm.subst sub rth
                  val th = Thm.resolve lit th rth
                  val new = LiteralSet.delete (Thm.clause rth) lit'
                  val news = LiteralSet.union new news
                in
                  (news,th)
                end
            end

      fun red (news,th) =
          if LiteralSet.null news then th
          else red (LiteralSet.foldl red1 (LiteralSet.empty,th) news)
    in
      fn th => Rule.removeSym (red (Thm.clause th, th))
    end;

end
