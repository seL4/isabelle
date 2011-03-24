(* ========================================================================= *)
(* NAMES                                                                     *)
(* Copyright (c) 2004 Joe Hurd, distributed under the BSD License            *)
(* ========================================================================= *)

structure Name :> Name =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* A type of names.                                                          *)
(* ------------------------------------------------------------------------- *)

type name = string;

(* ------------------------------------------------------------------------- *)
(* A total ordering.                                                         *)
(* ------------------------------------------------------------------------- *)

val compare = String.compare;

fun equal n1 n2 = n1 = n2;

(* ------------------------------------------------------------------------- *)
(* Fresh variables.                                                          *)
(* ------------------------------------------------------------------------- *)

local
  val prefix  = "_";

  fun numName i = mkPrefix prefix (Int.toString i);
in
  fun newName () = numName (newInt ());

  fun newNames n = List.map numName (newInts n);
end;

fun variantPrime {avoid} =
    let
      fun variant n = if avoid n then variant (n ^ "'") else n
    in
      variant
    end;

local
  fun isDigitOrPrime c = c = #"'" orelse Char.isDigit c;
in
  fun variantNum {avoid} n =
      if not (avoid n) then n
      else
        let
          val n = stripSuffix isDigitOrPrime n

          fun variant i =
              let
                val n_i = n ^ Int.toString i
              in
                if avoid n_i then variant (i + 1) else n_i
              end
        in
          variant 0
        end;
end;

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty printing.                                              *)
(* ------------------------------------------------------------------------- *)

val pp = Print.ppString;

fun toString s : string = s;

fun fromString s : name = s;

end

structure NameOrdered =
struct type t = Name.name val compare = Name.compare end

structure NameMap = KeyMap (NameOrdered);

structure NameSet =
struct

local
  structure S = ElementSet (NameMap);
in
  open S;
end;

val pp =
    Print.ppMap
      toList
      (Print.ppBracket "{" "}" (Print.ppOpList "," Name.pp));

end
