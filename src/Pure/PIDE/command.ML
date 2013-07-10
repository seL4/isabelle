(*  Title:      Pure/PIDE/command.ML
    Author:     Makarius

Prover command execution: read -- eval -- print.
*)

signature COMMAND =
sig
  type eval_process
  type eval = {exec_id: Document_ID.exec, eval_process: eval_process}
  val eval_result_state: eval -> Toplevel.state
  type print_process
  type print = {name: string, pri: int, exec_id: Document_ID.exec, print_process: print_process}
  type exec = eval * print list
  val no_exec: exec
  val exec_ids: exec option -> Document_ID.exec list
  val stable_eval: eval -> bool
  val stable_print: print -> bool
  val read: (unit -> theory) -> Token.T list -> Toplevel.transition
  val eval: (unit -> theory) -> Token.T list -> eval -> eval
  val print: bool -> string -> eval -> print list -> print list option
  type print_fn = Toplevel.transition -> Toplevel.state -> unit
  val print_function: {name: string, pri: int} -> (string -> print_fn option) -> unit
  val no_print_function: string -> unit
  val execute: exec -> unit
end;

structure Command: COMMAND =
struct

(** memo results -- including physical interrupts! **)

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
              let val res = Exn.capture e ();  (*sic!*)
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



(** main phases of execution **)

(* basic type definitions *)

type eval_state =
  {failed: bool, malformed: bool, command: Toplevel.transition, state: Toplevel.state};
val init_eval_state =
  {failed = false, malformed = false, command = Toplevel.empty, state = Toplevel.toplevel};

type eval_process = eval_state memo;
type eval = {exec_id: Document_ID.exec, eval_process: eval_process};

fun eval_result ({eval_process, ...}: eval) = memo_result eval_process;
val eval_result_state = #state o eval_result;

type print_process = unit memo;
type print = {name: string, pri: int, exec_id: Document_ID.exec, print_process: print_process};

type exec = eval * print list;
val no_exec: exec = ({exec_id = Document_ID.none, eval_process = memo_value init_eval_state}, []);

fun exec_ids (NONE: exec option) = []
  | exec_ids (SOME ({exec_id, ...}, prints)) = exec_id :: map #exec_id prints;


(* stable results *)

fun stable_goals exec_id =
  not (Par_Exn.is_interrupted (Future.join_results (Goal.peek_futures exec_id)));

fun stable_eval ({exec_id, eval_process}: eval) =
  stable_goals exec_id andalso memo_stable eval_process;

fun stable_print ({exec_id, print_process, ...}: print) =
  stable_goals exec_id andalso memo_stable print_process;


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
  in {exec_id = exec_id, eval_process = memo process} end;

end;


(* print *)

type print_fn = Toplevel.transition -> Toplevel.state -> unit;

local

type print_function = string * (int * (string -> print_fn option));
val print_functions = Synchronized.var "Command.print_functions" ([]: print_function list);

fun print_error tr e =
  (Toplevel.setmp_thread_position tr o Runtime.controlled_execution) e () handle exn =>
    List.app (Future.error_msg (Toplevel.pos_of tr)) (ML_Compiler.exn_messages_ids exn);

in

fun print command_visible command_name eval old_prints =
  let
    fun new_print (name, (pri, get_print_fn)) =
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
          in {name = name, pri = pri, exec_id = exec_id, print_process = memo process} end;
      in
        (case Exn.capture (Runtime.controlled_execution get_print_fn) command_name of
          Exn.Res NONE => NONE
        | Exn.Res (SOME print_fn) => SOME (make_print false print_fn)
        | Exn.Exn exn => SOME (make_print true (fn _ => fn _ => reraise exn)))
      end;

    val new_prints =
      if command_visible then
        rev (Synchronized.value print_functions) |> map_filter (fn pr =>
          (case find_first (equal (fst pr) o #name) old_prints of
            SOME print => if stable_print print then SOME print else new_print pr
          | NONE => new_print pr))
      else filter stable_print old_prints;
  in
    if eq_list (op = o pairself #exec_id) (old_prints, new_prints) then NONE
    else SOME new_prints
  end;

fun print_function {name, pri} f =
  Synchronized.change print_functions (fn funs =>
   (if not (AList.defined (op =) funs name) then ()
    else warning ("Redefining command print function: " ^ quote name);
    AList.update (op =) (name, (pri, f)) funs));

fun no_print_function name =
  Synchronized.change print_functions (filter_out (equal name o #1));

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


(* overall execution process *)

fun run_print ({name, pri, print_process, ...}: print) =
  (if Multithreading.enabled () then
    memo_fork {name = name, group = NONE, deps = [], pri = pri, interrupts = true}
  else memo_eval) print_process;

fun execute (({eval_process, ...}, prints): exec) =
  (memo_eval eval_process; List.app run_print prints);

end;

