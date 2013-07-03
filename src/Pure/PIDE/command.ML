(*  Title:      Pure/PIDE/command.ML
    Author:     Makarius

Prover command execution.
*)

signature COMMAND =
sig
  type span = Token.T list
  val range: span -> Position.range
  val proper_range: span -> Position.range
  type 'a memo
  val memo: (unit -> 'a) -> 'a memo
  val memo_value: 'a -> 'a memo
  val memo_eval: 'a memo -> 'a
  val memo_result: 'a memo -> 'a
  val read: span -> Toplevel.transition
  val eval: span -> Toplevel.transition ->
    Toplevel.state * {malformed: bool} -> {failed: bool} * (Toplevel.state * {malformed: bool})
  type print = {name: string, pri: int, pr: unit lazy}
  val print: Toplevel.state -> Toplevel.transition -> Toplevel.state -> print list
  type print_function =
    {old_state: Toplevel.state, tr: Toplevel.transition, state: Toplevel.state} ->
      (unit -> unit) option
  val print_function: string -> int -> print_function -> unit
end;

structure Command: COMMAND =
struct

(* source *)

type span = Token.T list;

val range = Token.position_range_of;
val proper_range = Token.position_range_of o #1 o take_suffix Token.is_improper;


(* memo results *)

datatype 'a expr =
  Expr of unit -> 'a |
  Result of 'a Exn.result;

abstype 'a memo = Memo of 'a expr Synchronized.var
with

fun memo e = Memo (Synchronized.var "Command.memo" (Expr e));
fun memo_value a = Memo (Synchronized.var "Command.memo" (Result (Exn.Res a)));

fun memo_eval (Memo v) =
  (case Synchronized.value v of
    Result res => res
  | _ =>
      Synchronized.guarded_access v
        (fn Result res => SOME (res, Result res)
          | Expr e =>
              let val res = Exn.capture e ();  (*memoing of physical interrupts!*)
              in SOME (res, Result res) end))
  |> Exn.release;

fun memo_result (Memo v) =
  (case Synchronized.value v of
    Result res => Exn.release res
  | _ => raise Fail "Unfinished memo result");

end;


(* read *)

fun read span =
  let
    val outer_syntax = #2 (Outer_Syntax.get_syntax ());
    val command_reports = Outer_Syntax.command_reports outer_syntax;

    val proper_range = Position.set_range (proper_range span);
    val pos =
      (case find_first Token.is_command span of
        SOME tok => Token.position_of tok
      | NONE => proper_range);

    val (is_malformed, token_reports) = Thy_Syntax.reports_of_tokens span;
    val _ = Position.reports_text (token_reports @ maps command_reports span);
  in
    if is_malformed then Toplevel.malformed pos "Malformed command syntax"
    else
      (case Outer_Syntax.read_spans outer_syntax span of
        [tr] =>
          if Keyword.is_control (Toplevel.name_of tr) then
            Toplevel.malformed pos "Illegal control command"
          else tr
      | [] => Toplevel.ignored (Position.set_range (range span))
      | _ => Toplevel.malformed proper_range "Exactly one command expected")
      handle ERROR msg => Toplevel.malformed proper_range msg
  end;


(* eval *)

local

fun run int tr st =
  if Goal.future_enabled () andalso Keyword.is_diag (Toplevel.name_of tr) then
    (Goal.fork_params {name = "Toplevel.diag", pos = Toplevel.pos_of tr, pri = ~1}
      (fn () => Toplevel.command_exception int tr st); ([], SOME st))
  else Toplevel.command_errors int tr st;

fun check_cmts span tr st' =
  Toplevel.setmp_thread_position tr
    (fn () =>
      Outer_Syntax.side_comments span |> maps (fn cmt =>
        (Thy_Output.check_text (Token.source_position_of cmt) st'; [])
          handle exn => ML_Compiler.exn_messages_ids exn)) ();

fun proof_status tr st =
  (case try Toplevel.proof_of st of
    SOME prf => Toplevel.status tr (Proof.status_markup prf)
  | NONE => ());

in

fun eval span tr (st, {malformed}) =
  if malformed then
    ({failed = true}, (Toplevel.toplevel, {malformed = malformed}))
  else
    let
      val malformed' = Toplevel.is_malformed tr;
      val is_init = Toplevel.is_init tr;
      val is_proof = Keyword.is_proof (Toplevel.name_of tr);

      val _ = Multithreading.interrupted ();
      val _ = Toplevel.status tr Markup.running;
      val (errs1, result) = run (is_init orelse is_proof) (Toplevel.set_print false tr) st;
      val errs2 = (case result of NONE => [] | SOME st' => check_cmts span tr st');
      val errs = errs1 @ errs2;
      val _ = Toplevel.status tr Markup.finished;
      val _ = List.app (Future.error_msg (Toplevel.pos_of tr)) errs;
    in
      (case result of
        NONE =>
          let
            val _ = if null errs then Exn.interrupt () else ();
            val _ = Toplevel.status tr Markup.failed;
          in ({failed = true}, (st, {malformed = malformed'})) end
      | SOME st' =>
          let
            val _ = proof_status tr st';
          in ({failed = false}, (st', {malformed = malformed'})) end)
    end;

end;


(* print *)

type print_function =
  {old_state: Toplevel.state, tr: Toplevel.transition, state: Toplevel.state} ->
    (unit -> unit) option;

type print = {name: string, pri: int, pr: unit lazy};

local

val print_functions =
  Synchronized.var "Command.print_functions" ([]: (string * (int * print_function)) list);

in

fun print st tr st' =
  rev (Synchronized.value print_functions) |> map_filter (fn (name, (pri, f)) =>
    (case f {old_state = st, tr = tr, state = st'} of
      SOME pr =>
        SOME {name = name, pri = pri, pr = (Lazy.lazy o Toplevel.setmp_thread_position tr) pr}
    | NONE => NONE));

fun print_function name pri f =
  Synchronized.change print_functions (fn funs =>
   (if not (AList.defined (op =) funs name) then ()
    else warning ("Redefining command print function: " ^ quote name);
    AList.update (op =) (name, (pri, f)) funs));

end;

val _ = print_function "print_state" 0 (fn {tr, state, ...} =>
  let
    val is_init = Toplevel.is_init tr;
    val is_proof = Keyword.is_proof (Toplevel.name_of tr);
    val do_print =
      not is_init andalso
        (Toplevel.print_of tr orelse (is_proof andalso Toplevel.is_proof state));
  in if do_print then SOME (fn () => Toplevel.print_state false state) else NONE end);

end;

