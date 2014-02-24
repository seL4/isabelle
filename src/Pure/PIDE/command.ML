(*  Title:      Pure/PIDE/command.ML
    Author:     Makarius

Prover command execution: read -- eval -- print.
*)

signature COMMAND =
sig
  type blob = (string * string option) Exn.result
  val read_file: Path.T -> Position.T -> Path.T -> Token.file
  val read: (unit -> theory) -> Path.T -> blob list -> Token.T list -> Toplevel.transition
  type eval
  val eval_eq: eval * eval -> bool
  val eval_running: eval -> bool
  val eval_finished: eval -> bool
  val eval_result_state: eval -> Toplevel.state
  val eval: (unit -> theory) -> Path.T -> blob list -> Token.T list -> eval -> eval
  type print
  val print: bool -> (string * string list) list -> string ->
    eval -> print list -> print list option
  type print_fn = Toplevel.transition -> Toplevel.state -> unit
  type print_function =
    {command_name: string, args: string list} ->
      {delay: Time.time option, pri: int, persistent: bool, strict: bool, print_fn: print_fn} option
  val print_function: string -> print_function -> unit
  val no_print_function: string -> unit
  type exec = eval * print list
  val no_exec: exec
  val exec_ids: exec option -> Document_ID.exec list
  val exec: Document_ID.execution -> exec -> unit
end;

structure Command: COMMAND =
struct

(** memo results **)

datatype 'a expr =
  Expr of Document_ID.exec * (unit -> 'a) |
  Result of 'a Exn.result;

abstype 'a memo = Memo of 'a expr Synchronized.var
with

fun memo exec_id e = Memo (Synchronized.var "Command.memo" (Expr (exec_id, e)));
fun memo_value a = Memo (Synchronized.var "Command.memo" (Result (Exn.Res a)));

fun memo_result (Memo v) =
  (case Synchronized.value v of
    Expr (exec_id, _) => error ("Unfinished execution result: " ^ Document_ID.print exec_id)
  | Result res => Exn.release res);

fun memo_finished (Memo v) =
  (case Synchronized.value v of Expr _ => false | Result _ => true);

fun memo_exec execution_id (Memo v) =
  Synchronized.timed_access v (K (SOME Time.zeroTime))
    (fn expr =>
      (case expr of
        Expr (exec_id, body) =>
          uninterruptible (fn restore_attributes => fn () =>
            let val group = Future.worker_subgroup () in
              if Execution.running execution_id exec_id [group] then
                let
                  val res =
                    (body
                      |> restore_attributes
                      |> Future.task_context "Command.memo_exec" group
                      |> Exn.interruptible_capture) ();
                in SOME ((), Result res) end
              else SOME ((), expr)
            end) ()
      | Result _ => SOME ((), expr)))
  |> (fn NONE => error "Conflicting command execution" | _ => ());

fun memo_fork params execution_id (Memo v) =
  (case Synchronized.value v of
    Result _ => ()
  | _ => ignore ((singleton o Future.forks) params (fn () => memo_exec execution_id (Memo v))));

end;



(** main phases of execution **)

(* read *)

type blob = (string * string option) Exn.result;  (*file node name, digest or text*)

fun read_file master_dir pos src_path =
  let
    val full_path = File.check_file (File.full_path master_dir src_path);
    val _ = Position.report pos (Markup.path (Path.implode full_path));
  in {src_path = src_path, text = File.read full_path, pos = Path.position full_path} end;

fun resolve_files master_dir blobs toks =
  (case Thy_Syntax.parse_spans toks of
    [span] => span
      |> Thy_Syntax.resolve_files (fn cmd => fn (path, pos) =>
        let
          fun make_file src_path (Exn.Res (_, NONE)) =
                Exn.interruptible_capture (fn () => read_file master_dir pos src_path) ()
            | make_file src_path (Exn.Res (file, SOME text)) =
                let
                  val _ = Position.report pos (Markup.path file);
                  val file_pos =
                    Position.file file (*sic!*) |>
                    (case Position.get_id (Position.thread_data ()) of
                      NONE => I
                    | SOME exec_id => Position.put_id exec_id);
                in Exn.Res {src_path = src_path, text = text, pos = file_pos} end
            | make_file _ (Exn.Exn e) = Exn.Exn e;

          val src_paths = Keyword.command_files cmd path;
        in
          if null blobs then
            map2 make_file src_paths (map (K (Exn.Res ("", NONE))) src_paths)
          else if length src_paths = length blobs then
            map2 make_file src_paths blobs
          else error ("Misalignment of inlined files" ^ Position.here pos)
        end)
      |> Thy_Syntax.span_content
  | _ => toks);

fun read init master_dir blobs span =
  let
    val outer_syntax = #2 (Outer_Syntax.get_syntax ());
    val command_reports = Outer_Syntax.command_reports outer_syntax;

    val proper_range = Token.range_of (#1 (take_suffix Token.is_improper span));
    val pos =
      (case find_first Token.is_command span of
        SOME tok => Token.pos_of tok
      | NONE => #1 proper_range);

    val (is_malformed, token_reports) = Thy_Syntax.reports_of_tokens span;
    val _ = Position.reports_text (token_reports @ maps command_reports span);
  in
    if is_malformed then Toplevel.malformed pos "Malformed command syntax"
    else
      (case Outer_Syntax.read_spans outer_syntax (resolve_files master_dir blobs span) of
        [tr] =>
          if Keyword.is_control (Toplevel.name_of tr) then
            Toplevel.malformed pos "Illegal control command"
          else Toplevel.modify_init init tr
      | [] => Toplevel.ignored (#1 (Token.range_of span))
      | _ => Toplevel.malformed (#1 proper_range) "Exactly one command expected")
      handle ERROR msg => Toplevel.malformed (#1 proper_range) msg
  end;


(* eval *)

type eval_state =
  {failed: bool, malformed: bool, command: Toplevel.transition, state: Toplevel.state};
val init_eval_state =
  {failed = false, malformed = false, command = Toplevel.empty, state = Toplevel.toplevel};

datatype eval = Eval of {exec_id: Document_ID.exec, eval_process: eval_state memo};

fun eval_eq (Eval {exec_id, ...}, Eval {exec_id = exec_id', ...}) = exec_id = exec_id';

fun eval_running (Eval {exec_id, ...}) = Execution.is_running_exec exec_id;
fun eval_finished (Eval {eval_process, ...}) = memo_finished eval_process;

fun eval_result (Eval {eval_process, ...}) = memo_result eval_process;
val eval_result_state = #state o eval_result;

local

fun run int tr st =
  if Goal.future_enabled 1 andalso Keyword.is_diag (Toplevel.name_of tr) then
    (Execution.fork {name = "Toplevel.diag", pos = Toplevel.pos_of tr, pri = ~1}
      (fn () => Toplevel.command_exception int tr st); ([], SOME st))
  else Toplevel.command_errors int tr st;

fun check_cmts span tr st' =
  Toplevel.setmp_thread_position tr
    (fn () =>
      Outer_Syntax.side_comments span |> maps (fn cmt =>
        (Thy_Output.check_text (Token.source_position_of cmt) st'; [])
          handle exn =>
            if Exn.is_interrupt exn then reraise exn
            else ML_Compiler.exn_messages_ids exn)) ();

fun report tr m =
  Toplevel.setmp_thread_position tr (fn () => Output.report (Markup.markup_only m)) ();

fun status tr m =
  Toplevel.setmp_thread_position tr (fn () => Output.status (Markup.markup_only m)) ();

fun proof_status tr st =
  (case try Toplevel.proof_of st of
    SOME prf => status tr (Proof.status_markup prf)
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
      val _ = status tr Markup.running;
      val (errs1, result) = run (is_init orelse is_proof) (Toplevel.set_print false tr) st;
      val errs2 = (case result of NONE => [] | SOME st' => check_cmts span tr st');
      val errs = errs1 @ errs2;
      val _ = List.app (Future.error_msg (Toplevel.pos_of tr)) errs;
    in
      (case result of
        NONE =>
          let
            val _ = status tr Markup.failed;
            val _ = status tr Markup.finished;
            val _ = if null errs then (report tr Markup.bad; Exn.interrupt ()) else ();
          in {failed = true, malformed = malformed', command = tr, state = st} end
      | SOME st' =>
          let
            val _ = proof_status tr st';
            val _ = status tr Markup.finished;
          in {failed = false, malformed = malformed', command = tr, state = st'} end)
    end;

in

fun eval init master_dir blobs span eval0 =
  let
    val exec_id = Document_ID.make ();
    fun process () =
      let
        val tr =
          Position.setmp_thread_data (Position.id_only (Document_ID.print exec_id))
            (fn () => read init master_dir blobs span |> Toplevel.exec_id exec_id) ();
      in eval_state span tr (eval_result eval0) end;
  in Eval {exec_id = exec_id, eval_process = memo exec_id process} end;

end;


(* print *)

datatype print = Print of
 {name: string, args: string list, delay: Time.time option, pri: int, persistent: bool,
  exec_id: Document_ID.exec, print_process: unit memo};

type print_fn = Toplevel.transition -> Toplevel.state -> unit;

type print_function =
  {command_name: string, args: string list} ->
    {delay: Time.time option, pri: int, persistent: bool, strict: bool, print_fn: print_fn} option;

local

val print_functions =
  Synchronized.var "Command.print_functions" ([]: (string * print_function) list);

fun print_error tr e =
  (Toplevel.setmp_thread_position tr o Toplevel.controlled_execution) e ()
    handle exn =>
      if Exn.is_interrupt exn then reraise exn
      else List.app (Future.error_msg (Toplevel.pos_of tr)) (ML_Compiler.exn_messages_ids exn);

fun print_eq (Print {exec_id, ...}, Print {exec_id = exec_id', ...}) = exec_id = exec_id';

fun print_finished (Print {print_process, ...}) = memo_finished print_process;

fun print_persistent (Print {persistent, ...}) = persistent;

val overlay_ord = prod_ord string_ord (list_ord string_ord);

in

fun print command_visible command_overlays command_name eval old_prints =
  let
    val print_functions = Synchronized.value print_functions;

    fun make_print name args {delay, pri, persistent, strict, print_fn} =
      let
        val exec_id = Document_ID.make ();
        fun process () =
          let
            val {failed, command, state = st', ...} = eval_result eval;
            val tr = Toplevel.exec_id exec_id command;
          in
            if failed andalso strict then ()
            else print_error tr (fn () => print_fn tr st')
          end;
      in
        Print {
          name = name, args = args, delay = delay, pri = pri, persistent = persistent,
          exec_id = exec_id, print_process = memo exec_id process}
      end;

    fun bad_print name args exn =
      make_print name args {delay = NONE, pri = 0, persistent = false,
        strict = false, print_fn = fn _ => fn _ => reraise exn};

    fun new_print name args get_pr =
      let
        val params = {command_name = command_name, args = args};
      in
        (case Exn.capture (Toplevel.controlled_execution get_pr) params of
          Exn.Res NONE => NONE
        | Exn.Res (SOME pr) => SOME (make_print name args pr)
        | Exn.Exn exn => SOME (bad_print name args exn))
      end;

    fun get_print (a, b) =
      (case find_first (fn Print {name, args, ...} => name = a andalso args = b) old_prints of
        NONE =>
          (case AList.lookup (op =) print_functions a of
            NONE => SOME (bad_print a b (ERROR ("Missing print function " ^ quote a)))
          | SOME get_pr => new_print a b get_pr)
      | some => some);

    val new_prints =
      if command_visible then
        fold (fn (a, _) => cons (a, [])) print_functions command_overlays
        |> sort_distinct overlay_ord
        |> map_filter get_print
      else filter (fn print => print_finished print andalso print_persistent print) old_prints;
  in
    if eq_list print_eq (old_prints, new_prints) then NONE else SOME new_prints
  end;

fun print_function name f =
  Synchronized.change print_functions (fn funs =>
   (if not (AList.defined (op =) funs name) then ()
    else warning ("Redefining command print function: " ^ quote name);
    AList.update (op =) (name, f) funs));

fun no_print_function name =
  Synchronized.change print_functions (filter_out (equal name o #1));

end;

val _ =
  print_function "print_state"
    (fn {command_name, ...} =>
      SOME {delay = NONE, pri = 1, persistent = false, strict = true,
        print_fn = fn tr => fn st' =>
          let
            val is_init = Keyword.is_theory_begin command_name;
            val is_proof = Keyword.is_proof command_name;
            val do_print =
              not is_init andalso
                (Toplevel.print_of tr orelse (is_proof andalso Toplevel.is_proof st'));
          in if do_print then Toplevel.print_state false st' else () end});


(* combined execution *)

type exec = eval * print list;
val no_exec: exec =
  (Eval {exec_id = Document_ID.none, eval_process = memo_value init_eval_state}, []);

fun exec_ids NONE = []
  | exec_ids (SOME (Eval {exec_id, ...}, prints)) =
      exec_id :: map (fn Print {exec_id, ...} => exec_id) prints;

local

fun run_print execution_id (Print {name, delay, pri, print_process, ...}) =
  if Multithreading.enabled () orelse pri <= 0 then
    let
      val group = Future.worker_subgroup ();
      fun fork () =
        memo_fork {name = name, group = SOME group, deps = [], pri = pri, interrupts = true}
          execution_id print_process;
    in
      (case delay of
        NONE => fork ()
      | SOME d => ignore (Event_Timer.request (Time.+ (Time.now (), d)) fork))
    end
  else memo_exec execution_id print_process;

in

fun exec execution_id (Eval {eval_process, ...}, prints) =
  (memo_exec execution_id eval_process; List.app (run_print execution_id) prints);

end;

end;

