(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_util.ML
    Author:     Jasmin Blanchette, TU Muenchen

General-purpose functions used by the Sledgehammer modules.
*)

signature SLEDGEHAMMER_UTIL =
sig
  val plural_s : int -> string
  val serial_commas : string -> string list -> string list
  val simplify_spaces : string -> string
  val parse_bool_option : bool -> string -> string -> bool option
  val parse_time_option : string -> string -> Time.time option
  val subgoal_count : Proof.state -> int
  val normalize_chained_theorems : thm list -> thm list
  val reserved_isar_keyword_table : unit -> unit Symtab.table
end;

structure Sledgehammer_Util : SLEDGEHAMMER_UTIL =
struct

open ATP_Util

fun plural_s n = if n = 1 then "" else "s"

val serial_commas = Try.serial_commas
val simplify_spaces = strip_spaces false (K true)

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

val has_junk =
  exists (fn s => not (Symbol.is_digit s) andalso s <> ".") o raw_explode (* FIXME Symbol.explode (?) *)

fun parse_time_option _ "none" = NONE
  | parse_time_option name s =
    let val secs = if has_junk s then NONE else Real.fromString s in
      if is_none secs orelse Real.< (the secs, 0.0) then
        error ("Parameter " ^ quote name ^ " must be assigned a nonnegative \
               \number of seconds (e.g., \"60\", \"0.5\") or \"none\".")
      else
        SOME (seconds (the secs))
    end

val subgoal_count = Try.subgoal_count

val normalize_chained_theorems =
  maps (fn th => insert Thm.eq_thm_prop (zero_var_indexes th) [th])
fun reserved_isar_keyword_table () =
  Keyword.dest () |-> union (op =)
  |> map (rpair ()) |> Symtab.make

end;
