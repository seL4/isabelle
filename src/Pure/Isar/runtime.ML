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
  val exn_messages: (exn -> Position.T) -> exn -> (serial * string) list
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

    fun flatten _ (CONTEXT (ctxt, exn)) = flatten (SOME ctxt) exn
      | flatten context (Exn.EXCEPTIONS exns) = maps (flatten context) exns
      | flatten context exn =
          (case Par_Exn.dest exn of
            SOME exns => maps (flatten context) exns
          | NONE => [(context, Par_Exn.serial exn)]);

    fun exn_msgs (context, (i, exn)) =
      (case exn of
        EXCURSION_FAIL (exn, loc) =>
          map (apsnd (fn msg => msg ^ Markup.markup Markup.no_report ("\n" ^ loc)))
            (sorted_msgs context exn)
      | _ =>
        let
          val msg =
            (case exn of
              TERMINATE => "Exit"
            | TimeLimit.TimeOut => "Timeout"
            | TOPLEVEL_ERROR => "Error"
            | ERROR msg => msg
            | Fail msg => raised exn "Fail" [msg]
            | THEORY (msg, thys) =>
                raised exn "THEORY" (msg :: (if detailed then map Context.str_of_thy thys else []))
            | Ast.AST (msg, asts) =>
                raised exn "AST" (msg ::
                  (if detailed then map (Pretty.string_of o Ast.pretty_ast) asts else []))
            | TYPE (msg, Ts, ts) =>
                raised exn "TYPE" (msg ::
                  (if detailed then
                    if_context context Syntax.string_of_typ Ts @
                    if_context context Syntax.string_of_term ts
                   else []))
            | TERM (msg, ts) =>
                raised exn "TERM" (msg ::
                  (if detailed then if_context context Syntax.string_of_term ts else []))
            | THM (msg, i, thms) =>
                raised exn ("THM " ^ string_of_int i) (msg ::
                  (if detailed then if_context context Display.string_of_thm thms else []))
            | _ => raised exn (General.exnMessage exn) []);
        in [(i, msg)] end)
      and sorted_msgs context exn =
        sort_distinct (int_ord o pairself fst) (maps exn_msgs (flatten context exn));

  in sorted_msgs NONE e end;

fun exn_message exn_position exn =
  (case exn_messages exn_position exn of
    [] => "Interrupt"
  | msgs => cat_lines (map snd msgs));


(** controlled execution **)

fun debugging f x =
  if ! debug
  then exception_trace (fn () => f x)
  else f x;

fun controlled_execution f x =
  (f |> debugging |> Future.interruptible_task) x;

fun toplevel_error output_exn f x = f x
  handle exn =>
    if Exn.is_interrupt exn then reraise exn
    else
      let
        val opt_ctxt =
          (case Context.thread_data () of
            NONE => NONE
          | SOME context => try Context.proof_of context);
        val _ = output_exn (exn_context opt_ctxt exn);
      in raise TOPLEVEL_ERROR end;

end;

