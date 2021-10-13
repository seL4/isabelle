(*  Title:      Tools/try.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Makarius

Manager for tools that should be tried on conjectures.
*)

signature TRY =
sig
  val serial_commas: string -> string list -> string list
  val subgoal_count: Proof.state -> int
  type body = bool -> Proof.state -> bool * (string * string list)
  type tool = {name: string, weight: int, auto_option: string, body: body}
  val get_tools: theory -> tool list
  val try_tools: Proof.state -> (string * string) option
  val tool_setup: tool -> unit
end;

structure Try : TRY =
struct

(* helpers *)

fun serial_commas _ [] = ["??"]
  | serial_commas _ [s] = [s]
  | serial_commas conj [s1, s2] = [s1, conj, s2]
  | serial_commas conj [s1, s2, s3] = [s1 ^ ",", s2 ^ ",", conj, s3]
  | serial_commas conj (s :: ss) = s ^ "," :: serial_commas conj ss;

val subgoal_count = Logic.count_prems o Thm.prop_of o #goal o Proof.goal;


(* configuration *)

type body = bool -> Proof.state -> bool * (string * string list);
type tool = {name: string, weight: int, auto_option: string, body: body};

fun tool_ord (tool1: tool, tool2: tool) =
  prod_ord int_ord string_ord ((#weight tool1, #name tool1), (#weight tool2, #name tool2));

structure Data = Theory_Data
(
  type T = tool list;
  val empty = [];
  val extend = I;
  fun merge data : T = Ord_List.merge tool_ord data;
);

val get_tools = Data.get;

val register_tool = Data.map o Ord_List.insert tool_ord;


(* try command *)

fun try_tools state =
  if subgoal_count state = 0 then
    (writeln "No subgoal!"; NONE)
  else
    get_tools (Proof.theory_of state)
    |> tap (fn tools =>
               "Trying " ^ space_implode " "
                    (serial_commas "and" (map (quote o #name) tools)) ^ "..."
               |> writeln)
    |> Par_List.get_some
           (fn {name, body, ...} =>
               case try (body false) state of
                 SOME (true, (outcome_code, _)) => SOME (name, outcome_code)
               | _ => NONE)
    |> tap (fn NONE => writeln "Tried in vain" | _ => ());

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>try\<close>
    "try a combination of automatic proving and disproving tools"
    (Scan.succeed (Toplevel.keep_proof (ignore o try_tools o Toplevel.proof_of)));


(* asynchronous print function *)

fun print_function ({name, weight, auto_option, body}: tool) =
  Command.print_function ("auto_" ^ name)
    (fn {keywords, command_name, ...} =>
      if Keyword.is_theory_goal keywords command_name andalso Options.default_bool auto_option then
        SOME
         {delay = SOME (seconds (Options.default_real \<^system_option>\<open>auto_time_start\<close>)),
          pri = ~ weight,
          persistent = true,
          strict = true,
          print_fn = fn _ => fn st =>
            let
              val state = Toplevel.proof_of st
                |> Proof.map_context (Context_Position.set_visible false)
              val auto_time_limit = Options.default_real \<^system_option>\<open>auto_time_limit\<close>
            in
              if auto_time_limit > 0.0 then
                (case Timeout.apply (seconds auto_time_limit) (fn () => body true state) () of
                  (true, (_, outcome)) => List.app Output.information outcome
                | _ => ())
              else ()
            end handle exn => if Exn.is_interrupt exn then Exn.reraise exn else ()}
      else NONE);


(* tool setup *)

fun tool_setup tool = (Theory.setup (register_tool tool); print_function tool);

end;
