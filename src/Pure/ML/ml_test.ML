(*  Title:      Pure/ML/ml_test.ML
    Author:     Makarius

Test of advanced ML compiler invocation in Poly/ML 5.3.
*)

structure ML_Test =
struct

(* eval ML source tokens *)

fun eval verbose pos toks =
  let
    val (print, err) = Output.ml_output;

    val input = toks |> map (fn tok =>
      (serial (), (String.explode (ML_Lex.text_of tok), ML_Lex.pos_of tok)));
    val index_pos = Inttab.lookup (Inttab.make (map (apsnd snd) input));

    fun pos_of ({file, startLine = line, startPosition = i, endPosition = j, ...}: location) =
      (case (index_pos i, index_pos j) of
        (SOME p, SOME q) => Position.encode_range (p, q)
      | (SOME p, NONE) => p
      | _ => Position.line_file line file);

    val in_buffer = ref (map (apsnd fst) input);
    val current_line = ref (the_default 1 (Position.line_of pos));
    fun get () =
      (case ! in_buffer of
        [] => NONE
      | (_, []) :: rest => (in_buffer := rest; get ())
      | (i, c :: cs) :: rest =>
          (in_buffer := (i, cs) :: rest;
           if c = #"\n" then current_line := ! current_line + 1 else ();
           SOME c));
    fun get_index () = (case ! in_buffer of [] => 0 | (i, _) :: _ => i);

    val out_buffer = ref ([]: string list);
    fun put s = out_buffer := s :: ! out_buffer;
    fun output () = implode (rev (! out_buffer));

    fun put_message {message, hard, location, context = _} =
     (put (if hard then "Error: " else "Warning: ");
      put (Pretty.string_of (Pretty.from_ML (pretty_ml message)));
      put (Position.str_of (pos_of location) ^ "\n"));

    val parameters =
     [PolyML.Compiler.CPOutStream put,
      PolyML.Compiler.CPNameSpace ML_Context.name_space,
      PolyML.Compiler.CPErrorMessageProc put_message,
      PolyML.Compiler.CPLineNo (fn () => ! current_line),
      PolyML.Compiler.CPLineOffset get_index,
      PolyML.Compiler.CPFileName (the_default "ML" (Position.file_of pos)),
      PolyML.Compiler.CPPrintInAlphabeticalOrder false];
    val _ =
      (while not (List.null (! in_buffer)) do
        PolyML.compiler (get, parameters) ())
      handle exn =>
       (put ("Exception- " ^ General.exnMessage exn ^ " raised");
        err (output ()); raise exn);
  in if verbose then print (output ()) else () end;


(* ML test command *)

fun ML_test (txt, pos) =
  let
    val _ = Position.report Markup.ML_source pos;
    val ants = ML_Lex.read_antiq (Symbol_Pos.explode (txt, pos), pos);
    val ((env, body), env_ctxt) = ML_Context.eval_antiquotes (ants, pos) (Context.thread_data ());

    val _ = Context.setmp_thread_data env_ctxt
        (fn () => (eval false Position.none env; Context.thread_data ())) ()
      |> (fn NONE => () | SOME context' => Context.>> (ML_Context.inherit_env context'));
    val _ = eval true pos body;
    val _ = eval false Position.none (ML_Lex.tokenize "structure Isabelle = struct end");
  in () end;


local structure P = OuterParse and K = OuterKeyword in

fun inherit_env (context as Context.Proof lthy) =
      Context.Proof (LocalTheory.map_contexts (ML_Context.inherit_env context) lthy)
  | inherit_env context = context;

val _ =
  OuterSyntax.command "ML_test" "advanced ML compiler test" (K.tag_ml K.thy_decl)
    (P.ML_source >> (fn src =>
      Toplevel.generic_theory (ML_Context.exec (fn () => ML_test src) #> inherit_env)));

end;

end;

