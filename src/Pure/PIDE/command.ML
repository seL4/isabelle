(*  Title:      Pure/PIDE/command.ML
    Author:     Makarius

Prover command execution: read -- eval -- print.
*)

signature COMMAND =
sig
  val read: (unit -> theory) -> Token.T list -> Toplevel.transition
  type eval
  val eval_result_state: eval -> Toplevel.state
  val eval_same: eval * eval -> bool
  val eval: (unit -> theory) -> Token.T list -> eval -> eval
  type print
  val print: bool -> string -> eval -> print list -> print list option
  type print_fn = Toplevel.transition -> Toplevel.state -> unit
  val print_function: {name: string, pri: int, persistent: bool} ->
    ({command_name: string} -> print_fn option) -> unit
  val no_print_function: string -> unit
  type exec = eval * print list
  val no_exec: exec
  val exec_ids: exec option -> Document_ID.exec list
  val exec: Execution.context -> exec -> unit
end;

structure Command: COMMAND =
struct

(** memo results -- including physical interrupts! **)

datatype 'a expr =
  Expr of Document_ID.exec * (unit -> 'a) |
  Result of 'a Exn.result;

abstype 'a memo = Memo of 'a expr Synchronized.var
with

fun memo exec_id e = Memo (Synchronized.var "Command.memo" (Expr (exec_id, e)));
fun memo_value a = Memo (Synchronized.var "Command.memo" (Result (Exn.Res a)));

fun memo_result (Memo v) =
  (case Synchronized.value v of
    Result res => Exn.release res
  | Expr (exec_id, _) => error ("Unfinished execution result: " ^ Document_ID.print exec_id));

fun memo_exec context (Memo v) =
  (case Synchronized.value v of
    Result res => res
  | Expr _ =>
      Synchronized.timed_access v (fn _ => SOME Time.zeroTime)
        (fn Result res => SOME (res, Result res)
          | expr as Expr (exec_id, e) =>
              uninterruptible (fn restore_attributes => fn () =>
                if Execution.running context exec_id then
                  let
                    val res = Exn.capture (restore_attributes e) ();
                    val _ = Execution.finished exec_id (not (Exn.is_interrupt_exn res));
                  in SOME (res, Result res) end
                else SOME (Exn.interrupt_exn, expr)) ())
      |> (fn NONE => error "Concurrent execution attempt" | SOME res => res))
  |> Exn.release |> ignore;

fun memo_fork params context (Memo v) =
  (case Synchronized.value v of
    Result _ => ()
  | _ => ignore ((singleton o Future.forks) params (fn () => memo_exec context (Memo v))));

end;


(** main phases of execution **)

(* read *)

fun read init span =
  let
    val outer_syntax = #2 (Outer_Syntax.get_syntax ());
    val command_reports = Outer_Syntax.command_reports outer_syntax;

    val proper_range =
      Position.set_range (Token.position_range_of (#1 (take_suffix Token.is_improper span)));
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
          else Toplevel.modify_init init tr
      | [] => Toplevel.ignored (Position.set_range (Token.position_range_of span))
      | _ => Toplevel.malformed proper_range "Exactly one command expected")
      handle ERROR msg => Toplevel.malformed proper_range msg
  end;


(* eval *)

type eval_state =
  {failed: bool, malformed: bool, command: Toplevel.transition, state: Toplevel.state};
val init_eval_state =
  {failed = false, malformed = false, command = Toplevel.empty, state = Toplevel.toplevel};

datatype eval = Eval of {exec_id: Document_ID.exec, eval_process: eval_state memo};

fun eval_result (Eval {eval_process, ...}) = memo_result eval_process;
val eval_result_state = #state o eval_result;

fun eval_same (Eval {exec_id, ...}, Eval {exec_id = exec_id', ...}) =
  exec_id = exec_id' andalso Execution.is_stable exec_id;

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

fun eval_state span tr ({malformed, state = st, ...}: eval_state) =
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

in

fun eval init span eval0 =
  let
    val exec_id = Document_ID.make ();
    fun process () =
      let
        val tr =
          Position.setmp_thread_data (Position.id_only (Document_ID.print exec_id))
            (fn () => read init span |> Toplevel.exec_id exec_id) ();
      in eval_state span tr (eval_result eval0) end;
  in Eval {exec_id = exec_id, eval_process = memo exec_id process} end;

end;


(* print *)

datatype print = Print of
 {name: string, pri: int, persistent: bool,
  exec_id: Document_ID.exec, print_process: unit memo};

type print_fn = Toplevel.transition -> Toplevel.state -> unit;

local

type print_function = string * (int * bool * ({command_name: string} -> print_fn option));
val print_functions = Synchronized.var "Command.print_functions" ([]: print_function list);

fun print_error tr e =
  (Toplevel.setmp_thread_position tr o Runtime.controlled_execution) e () handle exn =>
    List.app (Future.error_msg (Toplevel.pos_of tr)) (ML_Compiler.exn_messages_ids exn);

fun print_persistent (Print {persistent, ...}) = persistent;
fun print_stable (Print {exec_id, ...}) = Execution.is_stable exec_id;
fun print_eq (Print {exec_id, ...}, Print {exec_id = exec_id', ...}) = exec_id = exec_id';

in

fun print command_visible command_name eval old_prints =
  let
    fun new_print (name, (pri, persistent, get_fn)) =
      let
        fun make_print strict print_fn =
          let
            val exec_id = Document_ID.make ();
            fun process () =
              let
                val {failed, command, state = st', ...} = eval_result eval;
                val tr = Toplevel.exec_id exec_id command;
              in
                if failed andalso not strict then ()
                else print_error tr (fn () => print_fn tr st')
              end;
          in
           Print {
             name = name, pri = pri, persistent = persistent,
             exec_id = exec_id, print_process = memo exec_id process}
          end;
      in
        (case Exn.capture (Runtime.controlled_execution get_fn) {command_name = command_name} of
          Exn.Res NONE => NONE
        | Exn.Res (SOME print_fn) => SOME (make_print false print_fn)
        | Exn.Exn exn => SOME (make_print true (fn _ => fn _ => reraise exn)))
      end;

    val new_prints =
      if command_visible then
        rev (Synchronized.value print_functions) |> map_filter (fn pr =>
          (case find_first (fn Print {name, ...} => name = fst pr) old_prints of
            SOME print => if print_stable print then SOME print else new_print pr
          | NONE => new_print pr))
      else filter (fn print => print_persistent print andalso print_stable print) old_prints;
  in
    if eq_list print_eq (old_prints, new_prints) then NONE else SOME new_prints
  end;

fun print_function {name, pri, persistent} f =
  Synchronized.change print_functions (fn funs =>
   (if not (AList.defined (op =) funs name) then ()
    else warning ("Redefining command print function: " ^ quote name);
    AList.update (op =) (name, (pri, persistent, f)) funs));

fun no_print_function name =
  Synchronized.change print_functions (filter_out (equal name o #1));

end;

val _ =
  print_function {name = "print_state", pri = 0, persistent = true}
    (fn {command_name} => SOME (fn tr => fn st' =>
      let
        val is_init = Keyword.is_theory_begin command_name;
        val is_proof = Keyword.is_proof command_name;
        val do_print =
          not is_init andalso
            (Toplevel.print_of tr orelse (is_proof andalso Toplevel.is_proof st'));
      in if do_print then Toplevel.print_state false st' else () end));


(* combined execution *)

type exec = eval * print list;
val no_exec: exec =
  (Eval {exec_id = Document_ID.none, eval_process = memo_value init_eval_state}, []);

fun exec_ids NONE = []
  | exec_ids (SOME (Eval {exec_id, ...}, prints)) =
      exec_id :: map (fn Print {exec_id, ...} => exec_id) prints;

local

fun run_print context (Print {name, pri, print_process, ...}) =
  (if Multithreading.enabled () then
    memo_fork {name = name, group = NONE, deps = [], pri = pri, interrupts = true}
  else memo_exec) context print_process;

in

fun exec context (Eval {eval_process, ...}, prints) =
  (memo_exec context eval_process; List.app (run_print context) prints);

end;

end;

