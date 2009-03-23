(*  Title:      Pure/ML/ml_parse.ML
    Author:     Makarius

Minimal parsing for SML -- fixing integer numerals.
*)

signature ML_PARSE =
sig
  val fix_ints: string -> string
  val global_context: use_context
end;

structure ML_Parse: ML_PARSE =
struct

structure T = ML_Lex;


(** error handling **)

fun !!! scan =
  let
    fun get_pos [] = " (past end-of-file!)"
      | get_pos (tok :: _) = Position.str_of (T.pos_of tok);

    fun err (toks, NONE) = "SML syntax error" ^ get_pos toks
      | err (toks, SOME msg) = "SML syntax error" ^ get_pos toks ^ ": " ^ msg;
  in Scan.!! err scan end;

fun bad_input x =
  (Scan.some (fn tok => (case T.kind_of tok of T.Error msg => SOME msg | _ => NONE)) :|--
    (fn msg => Scan.fail_with (K msg))) x;


(** basic parsers **)

fun $$$ x =
  Scan.one (fn tok => T.kind_of tok = T.Keyword andalso T.content_of tok = x) >> T.content_of;
val int = Scan.one (fn tok => T.kind_of tok = T.Int) >> T.content_of;

val regular = Scan.one T.is_regular >> T.content_of;
val improper = Scan.one T.is_improper >> T.content_of;

val blanks = Scan.repeat improper >> implode;


(* fix_ints *)

(*approximation only -- corrupts numeric record field patterns *)
val fix_int =
  $$$ "#" ^^ blanks ^^ int ||
  ($$$ "infix" || $$$ "infixr") ^^ blanks ^^ int ||
  int >> (fn x => "(" ^ x ^ ":int)") ||
  regular ||
  bad_input;

fun do_fix_ints s =
  Source.of_string s
  |> T.source
  |> Source.source T.stopper (Scan.bulk (!!! fix_int)) NONE
  |> Source.exhaust
  |> implode;

val fix_ints = if ml_system_fix_ints then do_fix_ints else I;


(* global use_context *)

val global_context: use_context =
 {tune_source = fix_ints,
  name_space = ML_Name_Space.global,
  str_of_pos = Position.str_of oo Position.line_file,
  print = writeln,
  error = error};

end;
