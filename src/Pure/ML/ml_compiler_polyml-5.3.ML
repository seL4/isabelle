(*  Title:      Pure/ML/ml_compiler_polyml-5.3.ML
    Author:     Makarius

Advanced runtime compilation for Poly/ML 5.3.0.
*)

signature ML_COMPILER =
sig
  val exn_position: exn -> Position.T
  val exn_message: exn -> string
  val eval: bool -> Position.T -> ML_Lex.token list -> unit
end

structure ML_Compiler: ML_COMPILER =
struct

(* source locations *)

fun position_of (loc: PolyML.location) =
  let
    val {file = text, startLine = line, startPosition = offset,
      endLine = end_line, endPosition = end_offset} = loc;
    val loc_props =
      (case YXML.parse text of
        XML.Elem (e, atts, _) => if e = Markup.positionN then atts else []
      | XML.Text s => Position.file_name s);
  in
    Position.value Markup.lineN line @
    Position.value Markup.offsetN offset @
    Position.value Markup.end_lineN end_line @
    Position.value Markup.end_offsetN end_offset @
    loc_props
  end |> Position.of_properties;

fun exn_position exn =
  (case PolyML.exceptionLocation exn of
    NONE => Position.none
  | SOME loc => position_of loc);

val exn_message = Runtime.exn_message exn_position;


(* parse trees *)

fun report_parse_tree depth space =
  let
    fun report_decl markup loc decl =
      Position.report_text Markup.ML_ref (position_of loc)
        (Markup.markup (Markup.properties (Position.properties_of (position_of decl)) markup) "");
    fun report loc (PolyML.PTtype types) =
          PolyML.NameSpace.displayTypeExpression (types, depth, space)
          |> pretty_ml |> Pretty.from_ML |> Pretty.string_of
          |> Position.report_text Markup.ML_typing (position_of loc)
      | report loc (PolyML.PTdeclaredAt decl) = report_decl Markup.ML_def loc decl
      | report loc (PolyML.PTopenedAt decl) = report_decl Markup.ML_open loc decl
      | report loc (PolyML.PTstructureAt decl) = report_decl Markup.ML_struct loc decl
      | report _ (PolyML.PTnextSibling tree) = report_tree (tree ())
      | report _ (PolyML.PTfirstChild tree) = report_tree (tree ())
      | report _ _ = ()
    and report_tree (loc, props) = List.app (report loc) props;
  in report_tree end;


(* eval ML source tokens *)

val offset_of = the_default 0 o Position.offset_of;

fun eval verbose pos toks =
  let
    val _ = Secure.secure_mltext ();
    val {name_space = space, print, error = err, ...} = ML_Env.local_context;


    (* input *)

    val location_props =
      op ^ (YXML.output_markup (Markup.position |> Markup.properties
            (filter (member (op =) [Markup.idN, Markup.fileN] o #1) (Position.properties_of pos))));

    val input = toks |> maps (fn tok =>
      let
        val syms = Symbol.explode (ML_Lex.check_content_of tok);
        val (ps, _) = fold_map (fn s => fn p => (p, Position.advance s p)) syms
          (Position.reset_range (ML_Lex.pos_of tok));
      in
        (ps ~~ syms) |> maps (fn (p, sym) =>
          map (pair (offset_of p)) (String.explode (Symbol.esc sym)))
      end);

    val end_pos =
      if null toks then Position.none
      else ML_Lex.end_pos_of (List.last toks);

    val input_buffer = Unsynchronized.ref (input @ [(offset_of end_pos, #"\n")]);
    val line = Unsynchronized.ref (the_default 1 (Position.line_of pos));

    fun get_offset () = (case ! input_buffer of [] => 0 | (i, _) :: _ => i);
    fun get () =
      (case ! input_buffer of
        [] => NONE
      | (_, c) :: rest =>
          (input_buffer := rest;
           if c = #"\n" then line := ! line + 1 else ();
           SOME c));


    (* output *)

    val output_buffer = Unsynchronized.ref Buffer.empty;
    fun output () = Buffer.content (! output_buffer);
    fun put s = Unsynchronized.change output_buffer (Buffer.add s);

    fun put_message {message, hard, location, context = _} =
     (put ((if hard then "Error" else "Warning") ^ Position.str_of (position_of location) ^ ":\n");
      put (Pretty.string_of (Pretty.from_ML (pretty_ml message)) ^ "\n"));


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
     ((case phase1 of
        NONE => ()
      | SOME parse_tree => report_parse_tree depth space parse_tree);
      (case phase2 of
        NONE => err "Static Errors"
      | SOME code =>
          apply_result
            ((code
              |> Runtime.debugging
              |> Runtime.toplevel_error (Output.error_msg o exn_message)) ())));


    (* compiler invocation *)

    val parameters =
     [PolyML.Compiler.CPOutStream put,
      PolyML.Compiler.CPNameSpace space,
      PolyML.Compiler.CPErrorMessageProc put_message,
      PolyML.Compiler.CPLineNo (fn () => ! line),
      PolyML.Compiler.CPLineOffset get_offset,
      PolyML.Compiler.CPFileName location_props,
      PolyML.Compiler.CPCompilerResultFun result_fun,
      PolyML.Compiler.CPPrintInAlphabeticalOrder false];
    val _ =
      (while not (List.null (! input_buffer)) do
        PolyML.compiler (get, parameters) ())
      handle exn =>
       (put ("Exception- " ^ General.exnMessage exn ^ " raised");
        err (output ()); reraise exn);
  in if verbose then print (output ()) else () end;

end;

