(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_util.ML
    Author:     Jasmin Blanchette, TU Muenchen

General-purpose functions used by the Sledgehammer modules.
*)

signature SLEDGEHAMMER_UTIL =
sig
  val pairf : ('a -> 'b) -> ('a -> 'c) -> 'a -> 'b * 'c
  val plural_s : int -> string
  val serial_commas : string -> string list -> string list
  val replace_all : string -> string -> string -> string
  val remove_all : string -> string -> string
  val timestamp : unit -> string
  val parse_bool_option : bool -> string -> string -> bool option
  val parse_time_option : string -> string -> Time.time option
end;
 
structure Sledgehammer_Util : SLEDGEHAMMER_UTIL =
struct

fun pairf f g x = (f x, g x)

fun plural_s n = if n = 1 then "" else "s"

fun serial_commas _ [] = ["??"]
  | serial_commas _ [s] = [s]
  | serial_commas conj [s1, s2] = [s1, conj, s2]
  | serial_commas conj [s1, s2, s3] = [s1 ^ ",", s2 ^ ",", conj, s3]
  | serial_commas conj (s :: ss) = s ^ "," :: serial_commas conj ss

fun replace_all bef aft =
  let
    fun aux seen "" = String.implode (rev seen)
      | aux seen s =
        if String.isPrefix bef s then
          aux seen "" ^ aft ^ aux [] (unprefix bef s)
        else
          aux (String.sub (s, 0) :: seen) (String.extract (s, 1, NONE))
  in aux [] end

fun remove_all bef = replace_all bef ""

val timestamp = Date.fmt "%Y-%m-%d %H:%M:%S" o Date.fromTimeLocal o Time.now

fun parse_bool_option option name s =
  (case s of
     "smart" => if option then NONE else raise Option
   | "false" => SOME false
   | "true" => SOME true
   | "" => SOME true
   | _ => raise Option)
  handle Option.Option =>
         let val ss = map quote ((option ? cons "smart") ["true", "false"]) in
           error ("Parameter " ^ quote name ^ " must be assigned " ^
                  space_implode " " (serial_commas "or" ss) ^ ".")
         end

fun parse_time_option _ "none" = NONE
  | parse_time_option name s =
    let
      val msecs =
        case space_explode " " s of
          [s1, "min"] => 60000 * the (Int.fromString s1)
        | [s1, "s"] => 1000 * the (Int.fromString s1)
        | [s1, "ms"] => the (Int.fromString s1)
        | _ => 0
    in
      if msecs <= 0 then
        error ("Parameter " ^ quote name ^ " must be assigned a positive time \
               \value (e.g., \"60 s\", \"200 ms\") or \"none\".")
      else
        SOME (Time.fromMilliseconds msecs)
    end

end;
