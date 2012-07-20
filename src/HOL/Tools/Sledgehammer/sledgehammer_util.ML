(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_util.ML
    Author:     Jasmin Blanchette, TU Muenchen

General-purpose functions used by the Sledgehammer modules.
*)

signature SLEDGEHAMMER_UTIL =
sig
  val plural_s : int -> string
  val serial_commas : string -> string list -> string list
  val simplify_spaces : string -> string
  val infinite_timeout : Time.time
  val time_mult : real -> Time.time -> Time.time
  val parse_bool_option : bool -> string -> string -> bool option
  val parse_time_option : string -> string -> Time.time option
  val subgoal_count : Proof.state -> int
  val reserved_isar_keyword_table : unit -> unit Symtab.table
  val thms_in_proof : unit Symtab.table option -> thm -> string list
end;

structure Sledgehammer_Util : SLEDGEHAMMER_UTIL =
struct

open ATP_Util

fun plural_s n = if n = 1 then "" else "s"

val serial_commas = Try.serial_commas
val simplify_spaces = strip_spaces false (K true)

val infinite_timeout = seconds 31536000.0 (* one year *)

fun time_mult k t =
  Time.fromMilliseconds (Real.ceil (k * Real.fromInt (Time.toMilliseconds t)))

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

fun reserved_isar_keyword_table () =
  Keyword.dest () |-> union (op =) |> map (rpair ()) |> Symtab.make

(* FIXME: Similar yet different code in "mirabelle.ML". The code here has a few
   fixes that seem to be missing over there; or maybe the two code portions are
   not doing the same? *)
fun fold_body_thms thm_name f =
  let
    fun app n (PBody {thms, ...}) =
      thms |> fold (fn (_, (name, _, body)) => fn accum =>
          let
            (* The second disjunct caters for the uncommon case where the proved
               theorem occurs in its own proof (e.g.,
               "Transitive_Closure.trancl_into_trancl"). *)
            val no_name = (name = "" orelse (n = 1 andalso name = thm_name))
            val accum =
              accum |> (if n = 1 andalso not no_name then f name else I)
            val n = n + (if no_name then 0 else 1)
          in accum |> (if n <= 1 then app n (Future.join body) else I) end)
  in fold (app 0) end

fun thms_in_proof all_names th =
  let
    val collect =
      case all_names of
        SOME names => (fn s => Symtab.defined names s ? insert (op =) s)
      | NONE => insert (op =)
    val names =
      [] |> fold_body_thms (Thm.get_name_hint th) collect [Thm.proof_body_of th]
  in names end

end;
