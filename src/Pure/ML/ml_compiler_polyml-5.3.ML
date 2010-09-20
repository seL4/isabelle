(*  Title:      Pure/ML/ml_compiler_polyml-5.3.ML
    Author:     Makarius

Advanced runtime compilation for Poly/ML 5.3.0.
*)

structure ML_Compiler: ML_COMPILER =
struct

(* source locations *)

fun position_of (loc: PolyML.location) =
  let
    val {file = text, startLine = line, startPosition = offset,
      endLine = end_line, endPosition = end_offset} = loc;
    val loc_props =
      (case YXML.parse text of
        XML.Elem ((e, atts), _) => if e = Markup.positionN then atts else []
      | XML.Text s => Position.file_name s);
  in
    Position.value Markup.lineN line @
    Position.value Markup.offsetN offset @
    Position.value Markup.end_lineN end_line @
    Position.value Markup.end_offsetN end_offset @
    loc_props
  end |> Position.of_properties;

fun offset_position_of loc =
  let val pos = position_of loc
  in if is_some (Position.offset_of pos) then pos else Position.none end;

fun exn_position exn =
  (case PolyML.exceptionLocation exn of
    NONE => Position.none
  | SOME loc => position_of loc);

val exn_messages = Runtime.exn_messages exn_position;
val exn_message = Runtime.exn_message exn_position;


(* parse trees *)

fun report_parse_tree depth space =
  let
    val report_text =
      (case Context.thread_data () of
        SOME (Context.Proof ctxt) => Context_Position.report_text ctxt
      | _ => Position.report_text);

    fun report_decl markup loc decl =
      report_text (offset_position_of loc) Markup.ML_ref
        (Markup.markup (Position.markup (position_of decl) markup) "");
    fun report loc (PolyML.PTtype types) =
          PolyML.NameSpace.displayTypeExpression (types, depth, space)
          |> pretty_ml |> Pretty.from_ML |> Pretty.string_of
          |> report_text (offset_position_of loc) Markup.ML_typing
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
    val space = ML_Env.name_space;


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

    val input_buffer = Unsynchronized.ref input;
    val line = Unsynchronized.ref (the_default 1 (Position.line_of pos));

    fun get_offset () = (case ! input_buffer of [] => 0 | (i, _) :: _ => i);
    fun get () =
      (case ! input_buffer of
        [] => NONE
      | (_, c) :: rest =>
          (input_buffer := rest;
           if c = #"\n" then line := ! line + 1 else ();
           SOME c));


    (* output channels *)

    val writeln_buffer = Unsynchronized.ref Buffer.empty;
    fun write s = Unsynchronized.change writeln_buffer (Buffer.add s);
    fun output_writeln () = writeln (Buffer.content (! writeln_buffer));

    val warnings = Unsynchronized.ref ([]: string list);
    fun warn msg = Unsynchronized.change warnings (cons msg);
    fun output_warnings () = List.app warning (rev (! warnings));

    val error_buffer = Unsynchronized.ref Buffer.empty;
    fun err msg = Unsynchronized.change error_buffer (Buffer.add msg #> Buffer.add "\n");
    fun flush_error () = writeln (Buffer.content (! error_buffer));
    fun raise_error msg = error (Buffer.content (Buffer.add msg (! error_buffer)));

    fun message {message = msg, hard, location = loc, context = _} =
      let
        val txt =
          Markup.markup Markup.no_report
            ((if hard then "Error" else "Warning") ^ Position.str_of (position_of loc) ^ ":\n") ^
          Pretty.string_of (Pretty.from_ML (pretty_ml msg)) ^
          Position.reported_text (offset_position_of loc)  Markup.report "";
      in if hard then err txt else warn txt end;


    (* results *)

    val depth = get_print_depth ();

    fun apply_result {fixes, types, signatures, structures, functors, values} =
      let
        fun display disp x =
          if depth > 0 then
            (disp x |> pretty_ml |> Pretty.from_ML |> Pretty.string_of |> write; write "\n")
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

    exception STATIC_ERRORS of unit;

    fun result_fun (phase1, phase2) () =
     ((case phase1 of
        NONE => ()
      | SOME parse_tree => report_parse_tree depth space parse_tree);
      (case phase2 of
        NONE => raise STATIC_ERRORS ()
      | SOME code =>
          apply_result
            ((code
              |> Runtime.debugging
              |> Runtime.toplevel_error (err o exn_message)) ())));


    (* compiler invocation *)

    val parameters =
     [PolyML.Compiler.CPOutStream write,
      PolyML.Compiler.CPNameSpace space,
      PolyML.Compiler.CPErrorMessageProc message,
      PolyML.Compiler.CPLineNo (fn () => ! line),
      PolyML.Compiler.CPLineOffset get_offset,
      PolyML.Compiler.CPFileName location_props,
      PolyML.Compiler.CPCompilerResultFun result_fun,
      PolyML.Compiler.CPPrintInAlphabeticalOrder false];
    val _ =
      (while not (List.null (! input_buffer)) do
        PolyML.compiler (get, parameters) ())
      handle exn =>
        if Exn.is_interrupt exn then reraise exn
        else
          let
            val exn_msg =
              (case exn of
                STATIC_ERRORS () => ""
              | Runtime.TOPLEVEL_ERROR => ""
              | _ => "Exception- " ^ General.exnMessage exn ^ " raised");
            val _ = output_warnings ();
            val _ = output_writeln ();
          in raise_error exn_msg end;
  in
    if verbose then (output_warnings (); flush_error (); output_writeln ())
    else ()
  end;

end;

