(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF FIRST ORDER LOGIC LITERALS           *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

structure LiteralNet :> LiteralNet =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* A type of literal sets that can be efficiently matched and unified.       *)
(* ------------------------------------------------------------------------- *)

type parameters = AtomNet.parameters;

type 'a literalNet =
    {positive : 'a AtomNet.atomNet,
     negative : 'a AtomNet.atomNet};

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

fun new parm = {positive = AtomNet.new parm, negative = AtomNet.new parm};

local
  fun pos ({positive,...} : 'a literalNet) = AtomNet.size positive;

  fun neg ({negative,...} : 'a literalNet) = AtomNet.size negative;
in
  fun size net = pos net + neg net;

  fun profile net = {positive = pos net, negative = neg net};
end;

fun insert {positive,negative} ((true,atm),a) =
    {positive = AtomNet.insert positive (atm,a), negative = negative}
  | insert {positive,negative} ((false,atm),a) =
    {positive = positive, negative = AtomNet.insert negative (atm,a)};

fun fromList parm l = foldl (fn (lit_a,n) => insert n lit_a) (new parm) l;

fun filter pred {positive,negative} =
    {positive = AtomNet.filter pred positive,
     negative = AtomNet.filter pred negative};

fun toString net = "LiteralNet[" ^ Int.toString (size net) ^ "]";

fun pp ppA =
    Parser.ppMap
      (fn {positive,negative} => (positive,negative))
      (Parser.ppBinop " + NEGATIVE" (AtomNet.pp ppA) (AtomNet.pp ppA));

(* ------------------------------------------------------------------------- *)
(* Matching and unification queries.                                         *)
(*                                                                           *)
(* These function return OVER-APPROXIMATIONS!                                *)
(* Filter afterwards to get the precise set of satisfying values.            *)
(* ------------------------------------------------------------------------- *)

fun match ({positive,...} : 'a literalNet) (true,atm) =
    AtomNet.match positive atm
  | match {negative,...} (false,atm) = AtomNet.match negative atm;

fun matched ({positive,...} : 'a literalNet) (true,atm) =
    AtomNet.matched positive atm
  | matched {negative,...} (false,atm) = AtomNet.matched negative atm;

fun unify ({positive,...} : 'a literalNet) (true,atm) =
    AtomNet.unify positive atm
  | unify {negative,...} (false,atm) = AtomNet.unify negative atm;

end
