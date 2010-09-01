(*  Title:      Pure/Isar/runtime.ML
    Author:     Makarius

Isar toplevel runtime support.
*)

signature RUNTIME =
sig
  exception UNDEF
  exception TERMINATE
  exception EXCURSION_FAIL of exn * string
  exception TOPLEVEL_ERROR
  val exn_context: Proof.context option -> exn -> exn
  val exn_messages: (exn -> Position.T) -> exn -> string list
  val exn_message: (exn -> Position.T) -> exn -> string
  val debugging: ('a -> 'b) -> 'a -> 'b
  val controlled_execution: ('a -> 'b) -> 'a -> 'b
  val toplevel_error: (exn -> unit) -> ('a -> 'b) -> 'a -> 'b
end;

structure Runtime: RUNTIME =
struct

(** exceptions **)

exception UNDEF;
exception TERMINATE;
exception EXCURSION_FAIL of exn * string;
exception TOPLEVEL_ERROR;


(* exn_context *)

exception CONTEXT of Proof.context * exn;

fun exn_context NONE exn = exn
  | exn_context (SOME ctxt) exn = CONTEXT (ctxt, exn);


(* exn_message *)

fun if_context NONE _ _ = []
  | if_context (SOME ctxt) f xs = map (f ctxt) xs;

fun exn_messages exn_position e =
  let
    fun raised exn name msgs =
      let val pos = Position.str_of (exn_position exn) in
        (case msgs of
          [] => "exception " ^ name ^ " raised" ^ pos
        | [msg] => "exception " ^ name ^ " raised" ^ pos ^ ": " ^ msg
        | _ => cat_lines (("exception " ^ name ^ " raised" ^ pos ^ ":") :: msgs))
      end;

    val detailed = ! Output.debugging;

    fun exn_msgs _ (CONTEXT (ctxt, exn)) = exn_msgs (SOME ctxt) exn
      | exn_msgs ctxt (Exn.EXCEPTIONS exns) = maps (exn_msgs ctxt) exns
      | exn_msgs ctxt (EXCURSION_FAIL (exn, loc)) =
          map (fn msg => msg ^ Markup.markup Markup.location ("\n" ^ loc)) (exn_msgs ctxt exn)
      | exn_msgs _ TERMINATE = ["Exit"]
      | exn_msgs _ Exn.Interrupt = []
      | exn_msgs _ TimeLimit.TimeOut = ["Timeout"]
      | exn_msgs _ TOPLEVEL_ERROR = ["Error"]
      | exn_msgs _ (SYS_ERROR msg) = ["## SYSTEM ERROR ##\n" ^ msg]
      | exn_msgs _ (ERROR msg) = [msg]
      | exn_msgs _ (exn as Fail msg) = [raised exn "Fail" [msg]]
      | exn_msgs _ (exn as THEORY (msg, thys)) =
          [raised exn "THEORY" (msg :: (if detailed then map Context.str_of_thy thys else []))]
      | exn_msgs _ (exn as Syntax.AST (msg, asts)) = [raised exn "AST" (msg ::
            (if detailed then map (Pretty.string_of o Syntax.pretty_ast) asts else []))]
      | exn_msgs ctxt (exn as TYPE (msg, Ts, ts)) = [raised exn "TYPE" (msg ::
            (if detailed then
              if_context ctxt Syntax.string_of_typ Ts @ if_context ctxt Syntax.string_of_term ts
             else []))]
      | exn_msgs ctxt (exn as TERM (msg, ts)) = [raised exn "TERM" (msg ::
            (if detailed then if_context ctxt Syntax.string_of_term ts else []))]
      | exn_msgs ctxt (exn as THM (msg, i, thms)) = [raised exn ("THM " ^ string_of_int i) (msg ::
            (if detailed then if_context ctxt Display.string_of_thm thms else []))]
      | exn_msgs _ exn = [raised exn (General.exnMessage exn) []];
  in exn_msgs NONE e end;

fun exn_message exn_position exn =
  (case exn_messages exn_position exn of
    [] => "Interrupt"
  | msgs => cat_lines msgs);



(** controlled execution **)

fun debugging f x =
  if ! Output.debugging then
    Exn.release (exception_trace (fn () =>
      Exn.Result (f x) handle
        exn as UNDEF => Exn.Exn exn
      | exn as EXCURSION_FAIL _ => Exn.Exn exn))
  else f x;

fun controlled_execution f =
  f
  |> debugging
  |> Future.interruptible_task;

fun toplevel_error output_exn f x =
  let val ctxt = Option.map Context.proof_of (Context.thread_data ())
  in f x handle exn => (output_exn (exn_context ctxt exn); raise TOPLEVEL_ERROR) end;

end;

