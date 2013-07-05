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
  val memo_fork: Future.params -> 'a memo -> unit
  val memo_result: 'a memo -> 'a
  val memo_stable: 'a memo -> bool
  val read: span -> Toplevel.transition
  type eval_state =
    {failed: bool, malformed: bool, command: Toplevel.transition, state: Toplevel.state}
  type eval = eval_state memo
  val no_eval: eval
  val eval: span -> Toplevel.transition -> eval_state -> eval_state
  type print_fn = Toplevel.transition -> Toplevel.state -> unit
  type print = {name: string, pri: int, exec_id: Document_ID.exec, print: unit memo}
  val print: string -> eval -> print list
  val print_function: {name: string, pri: int} -> (string -> print_fn option) -> unit
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

fun memo_fork params (Memo v) =
  (case Synchronized.value v of
    Result _ => ()
  | _ => ignore ((singleton o Future.forks) params (fn () => memo_eval (Memo v))));

fun memo_result (Memo v) =
  (case Synchronized.value v of
    Result res => Exn.release res
  | _ => raise Fail "Unfinished memo result");

fun memo_stable (Memo v) =
  (case Synchronized.value v of
    Expr _ => true
  | Result res => not (Exn.is_interrupt_exn res));

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

type eval_state =
  {failed: bool, malformed: bool, command: Toplevel.transition, state: Toplevel.state};
val no_eval_state: eval_state =
  {failed = false, malformed = false, command = Toplevel.empty, state = Toplevel.toplevel};

type eval = eval_state memo;
val no_eval = memo_value no_eval_state;

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

fun eval span tr ({malformed, state = st, ...}: eval_state) =
  if malformed then
    {failed = true, malformed = malformed, command = tr, state = Toplevel.toplevel}
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
          in {failed = true, malformed = malformed', command = tr, state = st} end
      | SOME st' =>
          let
            val _ = proof_status tr st';
          in {failed = false, malformed = malformed', command = tr, state = st'} end)
    end;

end;


(* print *)

type print = {name: string, pri: int, exec_id: Document_ID.exec, print: unit memo};
type print_fn = Toplevel.transition -> Toplevel.state -> unit;

local

type print_function = string * (int * (string -> print_fn option));
val print_functions = Synchronized.var "Command.print_functions" ([]: print_function list);

fun output_error tr exn =
  List.app (Future.error_msg (Toplevel.pos_of tr)) (ML_Compiler.exn_messages_ids exn);

fun print_error tr f x =
  (Toplevel.setmp_thread_position tr o Runtime.controlled_execution) f x
    handle exn => output_error tr exn;

in

fun print command_name eval =
  rev (Synchronized.value print_functions) |> map_filter (fn (name, (pri, get_print_fn)) =>
    (case Exn.capture (Runtime.controlled_execution get_print_fn) command_name of
      Exn.Res NONE => NONE
    | Exn.Res (SOME print_fn) =>
        let
          val exec_id = Document_ID.make ();
          fun body () =
            let
              val {failed, command, state = st', ...} = memo_result eval;
              val tr = Toplevel.put_id exec_id command;
            in if failed then () else print_error tr (fn () => print_fn tr st') () end;
        in SOME {name = name, pri = pri, exec_id = exec_id, print = memo body} end
    | Exn.Exn exn =>
        let
          val exec_id = Document_ID.make ();
          fun body () =
            let
              val {command, ...} = memo_result eval;
              val tr = Toplevel.put_id exec_id command;
            in output_error tr exn end;
        in SOME {name = name, pri = pri, exec_id = exec_id, print = memo body} end));

fun print_function {name, pri} f =
  Synchronized.change print_functions (fn funs =>
   (if not (AList.defined (op =) funs name) then ()
    else warning ("Redefining command print function: " ^ quote name);
    AList.update (op =) (name, (pri, f)) funs));

end;

val _ =
  print_function {name = "print_state", pri = 0} (fn command_name => SOME (fn tr => fn st' =>
    let
      val is_init = Keyword.is_theory_begin command_name;
      val is_proof = Keyword.is_proof command_name;
      val do_print =
        not is_init andalso
          (Toplevel.print_of tr orelse (is_proof andalso Toplevel.is_proof st'));
    in if do_print then Toplevel.print_state false st' else () end));

end;

