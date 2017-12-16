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
  val parse_time: string -> Time.time
  val print_time: Time.time -> string
end;

structure Value: VALUE =
struct

(* bool *)

fun parse_bool "true" = true
  | parse_bool "false" = false
  | parse_bool s = raise Fail ("Bad boolean " ^ quote s);

val print_bool = Bool.toString;


(* nat and int *)

val zero = ord "0";
val nine = ord "9";

fun parse_nat s =
  fold_string (fn c => fn n =>
    let val i = ord c in
      if zero <= i andalso i <= nine then 10 * n + (i - zero)
      else raise Fail ("Bad natural number " ^ quote s)
    end) s 0;

fun parse_int s =
  (case try (unprefix "-") s of
    NONE => parse_nat s
  | SOME s' => ~ (parse_nat s'))
  handle Fail _ => raise Fail ("Bad integer " ^ quote s);

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


(* time *)

fun parse_time s =
  (case Time.fromString s of
    SOME x => x
  | NONE => raise Fail ("Bad time " ^ quote s));

fun print_time x =
  if x < Time.zeroTime then "-" ^ Time.toString (Time.zeroTime - x)
  else Time.toString x;

end;
