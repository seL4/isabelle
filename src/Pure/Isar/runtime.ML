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
  val debug: bool Unsynchronized.ref
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

val debug = Unsynchronized.ref false;


(* exn_context *)

exception CONTEXT of Proof.context * exn;

fun exn_context NONE exn = exn
  | exn_context (SOME ctxt) exn = if Exn.is_interrupt exn then exn else CONTEXT (ctxt, exn);


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

    val detailed = ! debug;

    fun exn_msgs context exn =
      if Exn.is_interrupt exn then []
      else
        (case exn of
          Exn.EXCEPTIONS exns => maps (exn_msgs context) exns
        | CONTEXT (ctxt, exn) => exn_msgs (SOME ctxt) exn
        | EXCURSION_FAIL (exn, loc) =>
            map (fn msg => msg ^ Markup.markup Markup.no_report ("\n" ^ loc)) (exn_msgs context exn)
        | TERMINATE => ["Exit"]
        | TimeLimit.TimeOut => ["Timeout"]
        | TOPLEVEL_ERROR => ["Error"]
        | SYS_ERROR msg => ["## SYSTEM ERROR ##\n" ^ msg]
        | ERROR msg => [msg]
        | Fail msg => [raised exn "Fail" [msg]]
        | THEORY (msg, thys) =>
            [raised exn "THEORY" (msg :: (if detailed then map Context.str_of_thy thys else []))]
        | Syntax.AST (msg, asts) =>
            [raised exn "AST" (msg ::
              (if detailed then map (Pretty.string_of o Syntax.pretty_ast) asts else []))]
        | TYPE (msg, Ts, ts) =>
            [raised exn "TYPE" (msg ::
              (if detailed then
                if_context context Syntax.string_of_typ Ts @
                if_context context Syntax.string_of_term ts
               else []))]
        | TERM (msg, ts) =>
            [raised exn "TERM" (msg ::
              (if detailed then if_context context Syntax.string_of_term ts else []))]
        | THM (msg, i, thms) =>
            [raised exn ("THM " ^ string_of_int i) (msg ::
              (if detailed then if_context context Display.string_of_thm thms else []))]
        | _ => [raised exn (General.exnMessage exn) []]);
  in exn_msgs NONE e end;

fun exn_message exn_position exn =
  (case exn_messages exn_position exn of
    [] => "Interrupt"
  | msgs => cat_lines msgs);


(** controlled execution **)

fun debugging f x =
  if ! debug then
    Exn.release (exception_trace (fn () =>
      Exn.Result (f x) handle
        exn as UNDEF => Exn.Exn exn
      | exn as EXCURSION_FAIL _ => Exn.Exn exn))
  else f x;

fun controlled_execution f =
  f
  |> debugging
  |> Future.interruptible_task;

fun toplevel_error output_exn f x = f x
  handle exn =>
    if Exn.is_interrupt exn then reraise exn
    else
      let
        val ctxt = Option.map Context.proof_of (Context.thread_data ());
        val _ = output_exn (exn_context ctxt exn);
      in raise TOPLEVEL_ERROR end;

end;

