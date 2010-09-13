(* ========================================================================= *)
(* NAMES                                                                     *)
(* Copyright (c) 2004 Joe Hurd, distributed under the GNU GPL version 2      *)
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

  fun newNames n = map numName (newInts n);
end;

fun variantPrime acceptable =
    let
      fun variant n = if acceptable n then n else variant (n ^ "'")
    in
      variant
    end;

local
  fun isDigitOrPrime #"'" = true
    | isDigitOrPrime c = Char.isDigit c;
in
  fun variantNum acceptable n =
      if acceptable n then n
      else
        let
          val n = stripSuffix isDigitOrPrime n

          fun variant i =
              let
                val n_i = n ^ Int.toString i
              in
                if acceptable n_i then n_i else variant (i + 1)
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
