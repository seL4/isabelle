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
  type exn_info = {exn_position: exn -> Position.T, pretty_exn: exn -> Pretty.T}
  type error = ((serial * string) * string option)
  val exn_messages_ids: exn_info -> exn -> error list
  val exn_messages: exn_info -> exn -> (serial * string) list
  val exn_message: exn_info -> exn -> string
  val exception_trace_raw: Config.raw
  val exception_trace: bool Config.T
  val debugging: (exn -> string) -> Context.generic option -> ('a -> 'b) -> 'a -> 'b
  val controlled_execution: (exn -> string) -> Context.generic option -> ('a -> 'b) -> 'a -> 'b
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
  | exn_context (SOME ctxt) exn = if Exn.is_interrupt exn then exn else CONTEXT (ctxt, exn);


(* exn_message *)

type exn_info = {exn_position: exn -> Position.T, pretty_exn: exn -> Pretty.T};
type error = ((serial * string) * string option);

local

fun robust f x =
  (case try f x of
    SOME s => s
  | NONE => Markup.markup Markup.intensify "<malformed>");

fun robust2 f x y = robust (fn () => f x y) ();

fun robust_context NONE _ _ = []
  | robust_context (SOME ctxt) f xs = map (robust2 f ctxt) xs;

fun identify exn =
  let
    val exn' = Par_Exn.identify [] exn;
    val exec_id = Properties.get (Exn_Properties.get exn') Markup.exec_idN;
    val i = Par_Exn.the_serial exn' handle Option.Option => serial ();
  in ((i, exn'), exec_id) end;

fun flatten _ (CONTEXT (ctxt, exn)) = flatten (SOME ctxt) exn
  | flatten context (Exn.EXCEPTIONS exns) = maps (flatten context) exns
  | flatten context exn =
      (case Par_Exn.dest exn of
        SOME exns => maps (flatten context) exns
      | NONE => [(context, identify exn)]);

in

fun exn_messages_ids {exn_position, pretty_exn} e =
  let
    fun raised exn name msgs =
      let val pos = Position.here (exn_position exn) in
        (case msgs of
          [] => "exception " ^ name ^ " raised" ^ pos
        | [msg] => "exception " ^ name ^ " raised" ^ pos ^ ": " ^ msg
        | _ =>
            cat_lines (("exception " ^ name ^ " raised" ^ pos ^ ":") ::
              map (Markup.markup Markup.item) msgs))
      end;

    fun exn_msgs (context, ((i, exn), id)) =
      (case exn of
        EXCURSION_FAIL (exn, loc) =>
          map (fn ((i, msg), id) => ((i, msg ^ Markup.markup Markup.no_report ("\n" ^ loc)), id))
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
                raised exn "THEORY" (msg :: map (robust Context.str_of_thy) thys)
            | Ast.AST (msg, asts) =>
                raised exn "AST" (msg :: map (robust (Pretty.string_of o Ast.pretty_ast)) asts)
            | TYPE (msg, Ts, ts) =>
                raised exn "TYPE" (msg ::
                  (robust_context context Syntax.string_of_typ Ts @
                    robust_context context Syntax.string_of_term ts))
            | TERM (msg, ts) =>
                raised exn "TERM" (msg :: robust_context context Syntax.string_of_term ts)
            | CTERM (msg, cts) =>
                raised exn "CTERM"
                  (msg :: robust_context context Syntax.string_of_term (map term_of cts))
            | THM (msg, i, thms) =>
                raised exn ("THM " ^ string_of_int i)
                  (msg :: robust_context context Display.string_of_thm thms)
            | _ => raised exn (robust (Pretty.string_of o pretty_exn) exn) []);
        in [((i, msg), id)] end)
      and sorted_msgs context exn =
        sort_distinct (int_ord o pairself (fst o fst)) (maps exn_msgs (flatten context exn));

  in sorted_msgs NONE e end;

end;

fun exn_messages exn_info exn = map #1 (exn_messages_ids exn_info exn);

fun exn_message exn_info exn =
  (case exn_messages exn_info exn of
    [] => "Interrupt"
  | msgs => cat_lines (map snd msgs));


(** controlled execution **)

val exception_trace_raw = Config.declare_option "ML_exception_trace";
val exception_trace = Config.bool exception_trace_raw;

fun exception_trace_enabled NONE =
      (Options.default_bool (Config.name_of exception_trace_raw) handle ERROR _ => false)
  | exception_trace_enabled (SOME context) = Config.get_generic context exception_trace;

fun debugging exn_message opt_context f x =
  if exception_trace_enabled opt_context
  then print_exception_trace exn_message (fn () => f x)
  else f x;

fun controlled_execution exn_message opt_context f x =
  (f |> debugging exn_message opt_context |> Future.interruptible_task) x;

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

