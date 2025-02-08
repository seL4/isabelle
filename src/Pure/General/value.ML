(*  Title:      Pure/General/value.ML
    Author:     Makarius

Plain values, represented as string.
*)

signature VALUE =
sig
  val parse_bool: string -> bool
  val print_bool: bool -> string
  val parse_nat: string -> int
  val parse_int: string -> int
  val print_int: int -> string
  val parse_real: string -> real
  val print_real: real -> string
end;

structure Value: VALUE =
struct

(* bool *)

fun parse_bool "true" = true
  | parse_bool "false" = false
  | parse_bool s = raise Fail ("Bad boolean " ^ quote s);

val print_bool = Bool.toString;


(* nat and int *)

local

val c0 = Char.ord #"0";
val c9 = Char.ord #"9";
val minus = Char.ord #"-";

in

fun parse_int str =
  let
    fun err () = raise Fail ("Bad integer " ^ quote str);
    val char = Char.ord o String.nth str;
    val n = size str;

    fun digits i a =
      if i = n then a
      else
        let val c = char i
        in if c0 <= c andalso c <= c9 then digits (i + 1) (10 * a + (c - c0)) else err () end;
  in
    if n = 0 then err ()
    else if char 0 <> minus then digits 0 0
    else if n = 1 then err ()
    else ~ (digits 1 0)
  end;

fun parse_nat str =
  let
    fun err () = raise Fail ("Bad natural number " ^ quote str);
    val i = parse_int str handle Fail _ => err ();
  in if i >= 0 then i else err () end;

end;

val print_int = signed_string_of_int;


(* real *)

fun parse_real s =
  (case Real.fromString s of
    SOME x => x
  | NONE => raise Fail ("Bad real " ^ quote s));

fun print_real x =
  let val s = signed_string_of_real x in
    (case space_explode "." s of
      [a, b] => if forall_string (fn c => c = "0") b then a else s
    | _ => s)
  end;

end;
