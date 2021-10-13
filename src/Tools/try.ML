(*  Title:      Tools/try.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Makarius

Manager for tools that should be tried on conjectures.
*)

signature TRY =
sig
  type tool = string * (int * string * (bool -> Proof.state -> bool * (string * string list)))

  val tryN: string

  val serial_commas: string -> string list -> string list
  val subgoal_count: Proof.state -> int
  val get_tools: theory -> tool list
  val try_tools: Proof.state -> (string * string) option
  val tool_setup: tool -> unit
end;

structure Try : TRY =
struct

type tool = string * (int * string * (bool -> Proof.state -> bool * (string * string list)));

val tryN = "try";


(* helpers *)

fun serial_commas _ [] = ["??"]
  | serial_commas _ [s] = [s]
  | serial_commas conj [s1, s2] = [s1, conj, s2]
  | serial_commas conj [s1, s2, s3] = [s1 ^ ",", s2 ^ ",", conj, s3]
  | serial_commas conj (s :: ss) = s ^ "," :: serial_commas conj ss;

val subgoal_count = Logic.count_prems o Thm.prop_of o #goal o Proof.goal;


(* configuration *)

fun tool_ord ((name1, (weight1, _, _)), (name2, (weight2, _, _))) =
  prod_ord int_ord string_ord ((weight1, name1), (weight2, name2));

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
                    (serial_commas "and" (map (quote o fst) tools)) ^ "..."
               |> writeln)
    |> Par_List.get_some
           (fn (name, (_, _, tool)) =>
               case try (tool false) state of
                 SOME (true, (outcome_code, _)) => SOME (name, outcome_code)
               | _ => NONE)
    |> tap (fn NONE => writeln "Tried in vain" | _ => ());

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>try\<close>
    "try a combination of automatic proving and disproving tools"
    (Scan.succeed (Toplevel.keep_proof (ignore o try_tools o Toplevel.proof_of)));


(* asynchronous print function *)

fun print_function ((name, (weight, auto, tool)): tool) =
  Command.print_function ("auto_" ^ name)
    (fn {keywords, command_name, ...} =>
      if Keyword.is_theory_goal keywords command_name andalso Options.default_bool auto then
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
                (case Timeout.apply (seconds auto_time_limit) (fn () => tool true state) () of
                  (true, (_, outcome)) => List.app Output.information outcome
                | _ => ())
              else ()
            end handle exn => if Exn.is_interrupt exn then Exn.reraise exn else ()}
      else NONE);


(* hybrid tool setup *)

fun tool_setup tool = (Theory.setup (register_tool tool); print_function tool);

end;
