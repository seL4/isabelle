(*  Title:      Pure/ML/ml_compiler_polyml-5.3.ML
    Author:     Makarius

Advanced runtime compilation for Poly/ML 5.3 (SVN 762).
*)

signature ML_COMPILER =
sig
  val eval: bool -> Position.T -> ML_Lex.token list -> unit
end

structure ML_Compiler: ML_COMPILER =
struct

(* original source positions *)

fun position_of (SOME context) (loc: PolyML.location) =
      (case pairself (ML_Env.token_position context) (#startPosition loc, #endPosition loc) of
        (SOME pos1, SOME pos2) => Position.encode_range (pos1, pos2)
      | (SOME pos, NONE) => pos
      | _ => Position.line_file (#startLine loc) (#file loc))
  | position_of NONE (loc: PolyML.location) = Position.line_file (#startLine loc) (#file loc);


(* parse trees *)

fun report_parse_tree context depth space =
  let
    val pos_of = position_of context;
    fun report loc (PolyML.PTtype types) =
          PolyML.NameSpace.displayTypeExpression (types, depth, space)
          |> pretty_ml |> Pretty.from_ML |> Pretty.string_of
          |> Position.report_text Markup.ML_typing (pos_of loc)
      | report loc (PolyML.PTdeclaredAt decl) =
          Markup.markup (Markup.properties (Position.properties_of (pos_of decl)) Markup.ML_def) ""
          |> Position.report_text Markup.ML_ref (pos_of loc)
      | report _ (PolyML.PTnextSibling tree) = report_tree (tree ())
      | report _ (PolyML.PTfirstChild tree) = report_tree (tree ())
      | report _ _ = ()
    and report_tree (loc, props) = List.app (report loc) props;
  in report_tree end;


(* eval ML source tokens *)

fun eval verbose pos toks =
  let
    val _ = Secure.secure_mltext ();
    val {name_space = space, print, error = err, ...} = ML_Env.local_context;


    (* input *)

    val input =
      if is_none (Context.thread_data ()) then map (pair 0) toks
      else Context.>>> (ML_Env.register_tokens toks);
    val input_buffer = ref (map (apsnd (String.explode o ML_Lex.text_of)) input);

    val current_line = ref (the_default 1 (Position.line_of pos));

    fun get_index () =
      the_default 0 (get_first (fn (_, []) => NONE | (i, _) => SOME i) (! input_buffer));

    fun get () =
      (case ! input_buffer of
        [] => NONE
      | (_, []) :: rest => (input_buffer := rest; get ())
      | (i, c :: cs) :: rest =>
          (input_buffer := (i, cs) :: rest;
           if c = #"\n" then current_line := ! current_line + 1 else ();
           SOME c));


    (* output *)

    val output_buffer = ref Buffer.empty;
    fun output () = Buffer.content (! output_buffer);
    fun put s = change output_buffer (Buffer.add s);

    fun put_message {message, hard, location, context = _} =
     (put (if hard then "Error: " else "Warning: ");
      put (Pretty.string_of (Pretty.from_ML (pretty_ml message)));
      put (Position.str_of (position_of (Context.thread_data ()) location) ^ "\n"));


    (* results *)

    val depth = get_print_depth ();

    fun apply_result {fixes, types, signatures, structures, functors, values} =
      let
        fun display disp x =
          if depth > 0 then
            (disp x |> pretty_ml |> Pretty.from_ML |> Pretty.string_of |> put; put "\n")
          else ();

        fun apply_fix (a, b) =
          (display PolyML.NameSpace.displayFix (a, b); #enterFix space (a, b));
        fun apply_type (a, b) =
          (display PolyML.NameSpace.displayType (b, depth, space); #enterType space (a, b));
        fun apply_sig (a, b) =
          (display PolyML.NameSpace.displaySig (b, depth, space); #enterSig space (a, b));
        fun apply_struct (a, b) =
          (display PolyML.NameSpace.displayStruct (b, depth, space); #enterStruct space (a, b));
        fun apply_funct (a, b) =
          (display PolyML.NameSpace.displayFunct (b, depth, space); #enterFunct space (a, b));
        fun apply_val (a, b) =
          (display PolyML.NameSpace.displayVal (b, depth, space); #enterVal space (a, b));
      in
        List.app apply_fix fixes;
        List.app apply_type types;
        List.app apply_sig signatures;
        List.app apply_struct structures;
        List.app apply_funct functors;
        List.app apply_val values
      end;

    fun result_fun (phase1, phase2) () =
     (case phase1 of NONE => ()
      | SOME parse_tree => report_parse_tree (Context.thread_data ()) depth space parse_tree;
      case phase2 of NONE => err "Static Errors"
      | SOME code => apply_result (code ()));  (* FIXME Toplevel.program *)


    (* compiler invocation *)

    val parameters =
     [PolyML.Compiler.CPOutStream put,
      PolyML.Compiler.CPNameSpace space,
      PolyML.Compiler.CPErrorMessageProc put_message,
      PolyML.Compiler.CPLineNo (fn () => ! current_line),
      PolyML.Compiler.CPFileName (the_default "ML" (Position.file_of pos)),
      PolyML.Compiler.CPLineOffset get_index,
      PolyML.Compiler.CPCompilerResultFun result_fun];
    val _ =
      (while not (List.null (! input_buffer)) do
        PolyML.compiler (get, parameters) ())
      handle exn =>
       (put ("Exception- " ^ General.exnMessage exn ^ " raised");
        err (output ()); raise exn);
  in if verbose then print (output ()) else () end;

end;

