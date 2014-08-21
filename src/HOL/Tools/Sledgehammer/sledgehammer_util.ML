(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_util.ML
    Author:     Jasmin Blanchette, TU Muenchen

General-purpose functions used by the Sledgehammer modules.
*)

signature SLEDGEHAMMER_UTIL =
sig
  val sledgehammerN : string
  val log2 : real -> real
  val map3 : ('a -> 'b -> 'c -> 'd) -> 'a list -> 'b list -> 'c list -> 'd list
  val app_hd : ('a -> 'a) -> 'a list -> 'a list
  val plural_s : int -> string
  val serial_commas : string -> string list -> string list
  val simplify_spaces : string -> string
  val with_cleanup : ('a -> unit) -> ('a -> 'b) -> 'a -> 'b
  val time_mult : real -> Time.time -> Time.time
  val parse_bool_option : bool -> string -> string -> bool option
  val parse_time : string -> string -> Time.time
  val subgoal_count : Proof.state -> int
  val reserved_isar_keyword_table : unit -> unit Symtab.table
  val thms_in_proof : int -> (string Symtab.table * string Symtab.table) option -> thm ->
    string list option
  val thms_of_name : Proof.context -> string -> thm list
  val one_day : Time.time
  val one_year : Time.time
  val with_vanilla_print_mode : ('a -> 'b) -> 'a -> 'b
  val hackish_string_of_term : Proof.context -> term -> string
  val spying : bool -> (unit -> Proof.state * int * string * string) -> unit
end;

structure Sledgehammer_Util : SLEDGEHAMMER_UTIL =
struct

open ATP_Util

val sledgehammerN = "sledgehammer"

val log10_2 = Math.log10 2.0
fun log2 n = Math.log10 n / log10_2

fun map3 xs = Ctr_Sugar_Util.map3 xs

fun app_hd f (x :: xs) = f x :: xs

fun plural_s n = if n = 1 then "" else "s"

val serial_commas = Try.serial_commas
val simplify_spaces = strip_spaces false (K true)

fun with_cleanup clean_up f x =
  Exn.capture f x
  |> tap (fn _ => clean_up x)
  |> Exn.release

fun time_mult k t = Time.fromMilliseconds (Real.ceil (k * Real.fromInt (Time.toMilliseconds t)))

fun parse_bool_option option name s =
  (case s of
     "smart" => if option then NONE else raise Option.Option
   | "false" => SOME false
   | "true" => SOME true
   | "" => SOME true
   | _ => raise Option.Option)
  handle Option.Option =>
    let val ss = map quote ((option ? cons "smart") ["true", "false"]) in
      error ("Parameter " ^ quote name ^ " must be assigned " ^
       space_implode " " (serial_commas "or" ss) ^ ".")
    end

val has_junk =
  exists (fn s => not (Symbol.is_digit s) andalso s <> ".") o raw_explode (* FIXME Symbol.explode (?) *)

fun parse_time name s =
  let val secs = if has_junk s then NONE else Real.fromString s in
    if is_none secs orelse Real.< (the secs, 0.0) then
      error ("Parameter " ^ quote name ^ " must be assigned a nonnegative \number of seconds \
        \(e.g., \"60\", \"0.5\") or \"none\".")
    else
      seconds (the secs)
  end

val subgoal_count = Try.subgoal_count

fun reserved_isar_keyword_table () =
  Keyword.dest () |-> union (op =) |> map (rpair ()) |> Symtab.make

exception TOO_MANY of unit

(* FIXME: Similar yet different code in "mirabelle.ML". The code here has a few fixes that seem to
   be missing over there; or maybe the two code portions are not doing the same? *)
fun fold_body_thm max_thms outer_name (map_plain_name, map_inclass_name) body =
  let
    fun app_thm map_name (_, (name, _, body)) (accum as (num_thms, names)) =
      let
        val (anonymous, enter_class) =
          (* The "name = outer_name" case caters for the uncommon case where the proved theorem
             occurs in its own proof (e.g., "Transitive_Closure.trancl_into_trancl"). *)
          if name = "" orelse name = outer_name then (true, false)
          else if map_inclass_name name = SOME outer_name then (true, true)
          else (false, false)
      in
        if anonymous then
          (case Future.peek body of
            SOME (Exn.Res the_body) =>
            app_body (if enter_class then map_inclass_name else map_name) the_body accum
          | NONE => accum)
        else
          (case map_name name of
            SOME name' =>
            if member (op =) names name' then accum
            else if num_thms = max_thms then raise TOO_MANY ()
            else (num_thms + 1, name' :: names)
          | NONE => accum)
      end
    and app_body map_name (PBody {thms, ...}) = fold (app_thm map_name) thms
  in
    snd (app_body map_plain_name body (0, []))
  end

fun thms_in_proof max_thms name_tabs th =
  (case try Thm.proof_body_of th of
    NONE => NONE
  | SOME body =>
    let val map_names = (case name_tabs of SOME p => pairself Symtab.lookup p | NONE => `I SOME) in
      SOME (fold_body_thm max_thms (Thm.get_name_hint th) map_names (Proofterm.strip_thm body))
      handle TOO_MANY () => NONE
    end)

fun thms_of_name ctxt name =
  let
    val lex = Keyword.get_lexicons
    val get = maps (Proof_Context.get_fact ctxt o fst)
  in
    Source.of_string name
    |> Symbol.source
    |> Token.source {do_recover = SOME false} lex Position.start
    |> Token.source_proper
    |> Source.source Token.stopper (Parse.xthms1 >> get) NONE
    |> Source.exhaust
  end

val one_day = seconds (24.0 * 60.0 * 60.0)
val one_year = seconds (365.0 * 24.0 * 60.0 * 60.0)

fun with_vanilla_print_mode f x =
  Print_Mode.setmp (filter (curry (op =) Symbol.xsymbolsN) (print_mode_value ())) f x

fun hackish_string_of_term ctxt =
  with_vanilla_print_mode (Syntax.string_of_term ctxt) #> unyxml #> simplify_spaces

val spying_version = "d"

fun spying false _ = ()
  | spying true f =
    let
      val (state, i, tool, message) = f ()
      val ctxt = Proof.context_of state
      val goal = Logic.get_goal (prop_of (#goal (Proof.goal state))) i
      val hash = String.substring (SHA1.rep (SHA1.digest (hackish_string_of_term ctxt goal)), 0, 12)
    in
      File.append (Path.explode "$ISABELLE_HOME_USER/spy_sledgehammer")
        (spying_version ^ " " ^ timestamp () ^ ": " ^ hash ^ ": " ^ tool ^ ": " ^ message ^ "\n")
    end

end;
