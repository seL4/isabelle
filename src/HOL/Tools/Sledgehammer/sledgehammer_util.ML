(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_util.ML
    Author:     Jasmin Blanchette, TU Muenchen

General-purpose functions used by the Sledgehammer modules.
*)

signature SLEDGEHAMMER_UTIL =
sig
  val sledgehammerN : string
  val log2 : real -> real
  val app_hd : ('a -> 'a) -> 'a list -> 'a list
  val plural_s : int -> string
  val serial_commas : string -> string list -> string list
  val simplify_spaces : string -> string
  val with_cleanup : ('a -> unit) -> ('a -> 'b) -> 'a -> 'b
  val infinite_timeout : Time.time
  val time_mult : real -> Time.time -> Time.time
  val parse_bool_option : bool -> string -> string -> bool option
  val parse_time_option : string -> string -> Time.time option
  val subgoal_count : Proof.state -> int
  val reserved_isar_keyword_table : unit -> unit Symtab.table
  val thms_in_proof :
    (string Symtab.table * string Symtab.table) option -> thm -> string list
  val thms_of_name : Proof.context -> string -> thm list
  val one_day : Time.time
  val one_year : Time.time
  val time_limit : Time.time option -> ('a -> 'b) -> 'a -> 'b
  val with_vanilla_print_mode : ('a -> 'b) -> 'a -> 'b
  val hackish_string_of_term : Proof.context -> term -> string
  val spying : bool -> (unit -> Proof.state * int * string * string) -> unit

  (** extrema **)
  val max : ('a * 'a -> order) -> 'a -> 'a -> 'a
  val max_option : ('a * 'a -> order) -> 'a option -> 'a option -> 'a option
  val max_list : ('a * 'a -> order) -> 'a list -> 'a option
end;

structure Sledgehammer_Util : SLEDGEHAMMER_UTIL =
struct

open ATP_Util

val sledgehammerN = "sledgehammer"

val log10_2 = Math.log10 2.0

fun log2 n = Math.log10 n / log10_2

fun app_hd f (x :: xs) = f x :: xs

fun plural_s n = if n = 1 then "" else "s"

val serial_commas = Try.serial_commas
val simplify_spaces = strip_spaces false (K true)

fun with_cleanup clean_up f x =
  Exn.capture f x
  |> tap (fn _ => clean_up x)
  |> Exn.release

val infinite_timeout = seconds 31536000.0 (* one year *)

fun time_mult k t =
  Time.fromMilliseconds (Real.ceil (k * Real.fromInt (Time.toMilliseconds t)))

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
fun fold_body_thms outer_name (map_plain_name, map_inclass_name) =
  let
    fun app map_name n (PBody {thms, ...}) =
      thms |> fold (fn (_, (name, _, body)) => fn accum =>
          let
            val collect = union (op =) o the_list o map_name
            (* The "name = outer_name" case caters for the uncommon case where
               the proved theorem occurs in its own proof (e.g.,
               "Transitive_Closure.trancl_into_trancl"). *)
            val (anonymous, enter_class) =
              if name = "" orelse (n = 1 andalso name = outer_name) then
                (true, false)
              else if n = 1 andalso map_inclass_name name = SOME outer_name then
                (true, true)
              else
                (false, false)
            val accum =
              accum |> (if n = 1 andalso not anonymous then collect name else I)
            val n = n + (if anonymous then 0 else 1)
          in
            accum
            |> (if n <= 1 then
                  app (if enter_class then map_inclass_name else map_name) n
                      (Future.join body)
                else
                  I)
          end)
  in fold (app map_plain_name 0) end

fun thms_in_proof name_tabs th =
  let
    val map_names =
      case name_tabs of
        SOME p => pairself Symtab.lookup p
      | NONE => `I SOME
    val names =
      fold_body_thms (Thm.get_name_hint th) map_names [Thm.proof_body_of th] []
  in names end

fun thms_of_name ctxt name =
  let
    val lex = Keyword.get_lexicons
    val get = maps (Proof_Context.get_fact ctxt o fst)
  in
    Source.of_string name
    |> Symbol.source
    |> Token.source {do_recover = SOME false} lex Position.start
    |> Token.source_proper
    |> Source.source Token.stopper (Parse_Spec.xthms1 >> get) NONE
    |> Source.exhaust
  end

val one_day = seconds (24.0 * 60.0 * 60.0)
val one_year = seconds (365.0 * 24.0 * 60.0 * 60.0)

fun time_limit NONE = I
  | time_limit (SOME delay) = TimeLimit.timeLimit delay

fun with_vanilla_print_mode f x =
  Print_Mode.setmp (filter (curry (op =) Symbol.xsymbolsN)
                           (print_mode_value ())) f x

fun hackish_string_of_term ctxt =
  with_vanilla_print_mode (Syntax.string_of_term ctxt) #> simplify_spaces

val spying_version = "c"

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

(** extrema **)

fun max ord x y = case ord(x,y) of LESS => y | _ => x

fun max_option ord = max (option_ord ord)

fun max_list ord xs = fold (SOME #> max_option ord) xs NONE

end;
