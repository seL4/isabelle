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
  val eval: span -> Toplevel.transition ->
    Toplevel.state * {malformed: bool} -> {failed: bool} * (Toplevel.state * {malformed: bool})
  val no_print: unit lazy
  val print: Toplevel.transition -> Toplevel.state -> unit lazy
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


(* side-comments *)

local

fun cmts (t1 :: t2 :: toks) =
      if Token.keyword_with (fn s => s = "--") t1 then t2 :: cmts toks
      else cmts (t2 :: toks)
  | cmts _ = [];

val span_cmts = filter Token.is_proper #> cmts;

in

fun check_cmts span tr st' =
  Toplevel.setmp_thread_position tr
    (fn () =>
      span_cmts span |> maps (fn cmt =>
        (Thy_Output.check_text (Token.source_position_of cmt) st'; [])
          handle exn => ML_Compiler.exn_messages_ids exn)) ();

end;


(* eval *)

local

fun run int tr st =
  if Goal.future_enabled () andalso Keyword.is_diag (Toplevel.name_of tr) then
    (Goal.fork_params {name = "Toplevel.diag", pos = Toplevel.pos_of tr, pri = ~1}
      (fn () => Toplevel.command_exception int tr st); ([], SOME st))
  else Toplevel.command_errors int tr st;

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

val no_print = Lazy.value ();

fun print tr st' =
  let
    val is_init = Toplevel.is_init tr;
    val is_proof = Keyword.is_proof (Toplevel.name_of tr);
    val do_print =
      not is_init andalso
        (Toplevel.print_of tr orelse (is_proof andalso Toplevel.is_proof st'));
  in
    if do_print then
      (Lazy.lazy o Toplevel.setmp_thread_position tr)
        (fn () => Toplevel.print_state false st')
    else no_print
  end;

end;

