(*  Title:      Pure/ML/ml_compiler.ML
    Author:     Makarius

Runtime compilation and evaluation.
*)

signature ML_COMPILER =
sig
  type flags =
    {environment: string, redirect: bool, verbose: bool, catch_all: bool,
      debug: bool option, writeln: string -> unit, warning: string -> unit}
  val debug_flags: bool option -> flags
  val flags: flags
  val verbose: bool -> flags -> flags
  val ML_catch_all: bool Config.T
  val eval: flags -> Position.T -> ML_Lex.token list -> unit
end;

structure ML_Compiler: ML_COMPILER =
struct

(* flags *)

type flags =
  {environment: string, redirect: bool, verbose: bool, catch_all: bool,
    debug: bool option, writeln: string -> unit, warning: string -> unit};

fun debug_flags opt_debug : flags =
  {environment = "", redirect = false, verbose = false, catch_all = false,
    debug = opt_debug, writeln = writeln, warning = warning};

val flags = debug_flags NONE;

fun verbose b ({environment, redirect, verbose = _, catch_all, debug, writeln, warning}: flags) =
  {environment = environment, redirect = redirect, verbose = b, catch_all = catch_all,
    debug = debug, writeln = writeln, warning = warning};


(* parse trees *)

fun breakpoint_position loc =
  let val pos = Position.no_range_position (Exn_Properties.position_of_polyml_location loc) in
    (case Position.offset_of pos of
      NONE => pos
    | SOME 1 => pos
    | SOME j =>
        Position.properties_of pos
        |> Properties.put (Markup.offsetN, Value.print_int (j - 1))
        |> Position.of_properties)
  end;

fun report_parse_tree redirect depth name_space parse_tree =
  let
    val reports_enabled =
      (case Context.get_generic_context () of
        SOME context => Context_Position.reports_enabled_generic context
      | NONE => Context_Position.reports_enabled0 ());
    fun is_reported pos = reports_enabled andalso Position.is_reported pos;


    (* syntax reports *)

    fun reported_types loc types =
      let val pos = Exn_Properties.position_of_polyml_location loc in
        is_reported pos ?
          let
            val xml =
              PolyML.NameSpace.Values.printType (types, depth, SOME name_space)
              |> Pretty.from_ML |> Pretty.string_of
              |> YXML.parse_body;
          in cons (pos, fn () => Markup.ML_typing, fn () => YXML.string_of_body xml) end
      end;

    fun reported_entity kind loc decl =
      let
        val pos = Exn_Properties.position_of_polyml_location loc;
        val def_pos = Exn_Properties.position_of_polyml_location decl;
      in
        (is_reported pos andalso pos <> def_pos) ?
          cons (pos, fn () => Position.entity_markup kind ("", def_pos), fn () => "")
      end;

    fun reported_entity_id def id loc =
      let
        val pos = Exn_Properties.position_of_polyml_location loc;
      in
        (is_reported pos andalso id <> 0) ?
          let
            fun markup () =
              (Markup.entityN, [(if def then Markup.defN else Markup.refN, Value.print_int id)]);
          in cons (pos, markup, fn () => "") end
      end;

    fun reported_completions loc names =
      let val pos = Exn_Properties.position_of_polyml_location loc in
        if is_reported pos andalso not (null names) then
          let
            val completion = Completion.names pos (map (fn a => (a, ("ML", a))) names);
            val xml = Completion.encode completion;
          in cons (pos, fn () => Markup.completion, fn () => YXML.string_of_body xml) end
        else I
      end;

    fun reported _ (PolyML.PTnextSibling tree) = reported_tree (tree ())
      | reported _ (PolyML.PTfirstChild tree) = reported_tree (tree ())
      | reported loc (PolyML.PTdefId id) = reported_entity_id true (FixedInt.toLarge id) loc
      | reported loc (PolyML.PTrefId id) = reported_entity_id false (FixedInt.toLarge id) loc
      | reported loc (PolyML.PTtype types) = reported_types loc types
      | reported loc (PolyML.PTdeclaredAt decl) = reported_entity Markup.ML_defN loc decl
      | reported loc (PolyML.PTcompletions names) = reported_completions loc names
      | reported _ _ = I
    and reported_tree (loc, props) = fold (reported loc) props;

    val persistent_reports = reported_tree parse_tree [];

    fun output () =
      persistent_reports
      |> map (fn (pos, markup, text) => Position.reported_text pos (markup ()) (text ()))
      |> Output.report;
    val _ =
      if not (null persistent_reports) andalso redirect andalso
        not (Options.default_bool "pide_reports") andalso Future.enabled ()
      then
        Execution.print
          {name = "ML_Compiler.report", pos = Position.thread_data (), pri = Task_Queue.urgent_pri}
          output
      else output ();


    (* breakpoints *)

    fun breakpoints _ (PolyML.PTnextSibling tree) = breakpoints_tree (tree ())
      | breakpoints _ (PolyML.PTfirstChild tree) = breakpoints_tree (tree ())
      | breakpoints loc (PolyML.PTbreakPoint b) =
          let val pos = breakpoint_position loc in
            if is_reported pos then
              let val id = serial ();
              in cons ((pos, Markup.ML_breakpoint id), (id, (b, pos))) end
            else I
          end
      | breakpoints _ _ = I
    and breakpoints_tree (loc, props) = fold (breakpoints loc) props;

    val all_breakpoints = rev (breakpoints_tree parse_tree []);
    val _ = Position.reports (map #1 all_breakpoints);
 in map (fn (_, (id, (b, pos))) => (id, (b, Position.dest pos))) all_breakpoints end;


(* eval ML source tokens *)

val ML_catch_all = Config.declare_bool ("ML_catch_all", \<^here>) (K false);

fun eval (flags: flags) pos toks =
  let
    val opt_context = Context.get_generic_context ();

    val env as {debug, name_space, add_breakpoints} =
      (case (ML_Recursive.get (), #environment flags <> "") of
        (SOME env, false) => env
      | _ =>
         {debug =
            (case #debug flags of
              SOME debug => debug
            | NONE => ML_Options.debugger_enabled opt_context),
          name_space = ML_Env.make_name_space (#environment flags),
          add_breakpoints = ML_Env.add_breakpoints});


    (* input *)

    val position_props =
      filter (fn (a, _) => a = Markup.labelN orelse a = Markup.fileN orelse a = Markup.idN)
        (Position.properties_of pos);
    val location_props = op ^ (YXML.output_markup (":", position_props));

    val {explode_token, ...} = ML_Env.operations opt_context (#environment flags);
    fun token_content tok = if ML_Lex.is_comment tok then NONE else SOME (`explode_token tok);

    val input_buffer =
      Unsynchronized.ref (map_filter token_content toks);

    fun get () =
      (case ! input_buffer of
        (c :: cs, tok) :: rest => (input_buffer := (cs, tok) :: rest; SOME c)
      | ([], _) :: rest => (input_buffer := rest; SOME #" ")
      | [] => NONE);

    fun get_pos () =
      (case ! input_buffer of
        (_ :: _, tok) :: _ => ML_Lex.pos_of tok
      | ([], tok) :: _ => ML_Lex.end_pos_of tok
      | [] => Position.none);


    (* output *)

    val writeln_buffer = Unsynchronized.ref Buffer.empty;
    fun write s = Unsynchronized.change writeln_buffer (Buffer.add s);
    fun output_writeln () = #writeln flags (trim_line (Buffer.content (! writeln_buffer)));

    val warnings = Unsynchronized.ref ([]: string list);
    fun warn msg = Unsynchronized.change warnings (cons msg);
    fun output_warnings () = List.app (#warning flags) (rev (! warnings));

    val error_buffer = Unsynchronized.ref Buffer.empty;
    fun err msg = Unsynchronized.change error_buffer (Buffer.add msg #> Buffer.add "\n");

    fun expose_error verbose =
      let
        val msg = Buffer.content (! error_buffer);
        val is_err = msg <> "";
        val _ = if is_err orelse verbose then (output_warnings (); output_writeln ()) else ();
      in if is_err then error (trim_line msg) else () end;

    fun message {message = msg, hard, location = loc, context = _} =
      let
        val pos = Exn_Properties.position_of_polyml_location loc;
        val s = Pretty.string_of (Pretty.from_ML msg);
        val catch_all =
          #catch_all flags orelse
            (case opt_context of
              NONE => false
            | SOME context => Config.get_generic context ML_catch_all);
        val is_err =
          hard orelse
            (not catch_all andalso
              String.isPrefix "Handler catches all exceptions" (XML.content_of (YXML.parse_body s)));
        val txt = (if is_err then "ML error" else "ML warning") ^ Position.here pos ^ ":\n" ^ s;
      in if is_err then err txt else warn txt end;


    (* results *)

    val depth = FixedInt.fromInt (ML_Print_Depth.get_print_depth ());

    fun apply_result {fixes, types, signatures, structures, functors, values} =
      let
        fun display disp x =
          if depth > 0 then
            (write (disp x |> Pretty.from_ML |> Pretty.string_of); write "\n")
          else ();

        fun apply_fix (a, b) =
          (#enterFix name_space (a, b);
            display PolyML.NameSpace.Infixes.print b);
        fun apply_type (a, b) =
          (#enterType name_space (a, b);
            display PolyML.NameSpace.TypeConstrs.print (b, depth, SOME name_space));
        fun apply_sig (a, b) =
          (#enterSig name_space (a, b);
            display PolyML.NameSpace.Signatures.print (b, depth, SOME name_space));
        fun apply_struct (a, b) =
          (#enterStruct name_space (a, b);
            display PolyML.NameSpace.Structures.print (b, depth, SOME name_space));
        fun apply_funct (a, b) =
          (#enterFunct name_space (a, b);
            display PolyML.NameSpace.Functors.print (b, depth, SOME name_space));
        fun apply_val (a, b) =
          (#enterVal name_space (a, b);
            display PolyML.NameSpace.Values.printWithType (b, depth, SOME name_space));
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
      | SOME parse_tree =>
          add_breakpoints (report_parse_tree (#redirect flags) depth name_space parse_tree));
      (case phase2 of
        NONE => raise STATIC_ERRORS ()
      | SOME code =>
          apply_result
            ((code
              |> Runtime.debugging opt_context
              |> Runtime.toplevel_error (err o Runtime.exn_message)) ())));


    (* compiler invocation *)

    val parameters =
     [PolyML.Compiler.CPOutStream write,
      PolyML.Compiler.CPNameSpace name_space,
      PolyML.Compiler.CPErrorMessageProc message,
      PolyML.Compiler.CPLineNo (the_default 0 o Position.line_of o get_pos),
      PolyML.Compiler.CPLineOffset (the_default 0 o Position.offset_of o get_pos),
      PolyML.Compiler.CPFileName location_props,
      PolyML.Compiler.CPPrintDepth ML_Print_Depth.get_print_depth,
      PolyML.Compiler.CPCompilerResultFun result_fun,
      PolyML.Compiler.CPPrintInAlphabeticalOrder false,
      PolyML.Compiler.CPDebug debug,
      PolyML.Compiler.CPBindingSeq serial];

    val _ =
      Isabelle_Thread.try_catch
        (fn () =>
          (while not (List.null (! input_buffer)) do
            ML_Recursive.recursive env (fn () => PolyML.compiler (get, parameters) ())))
        (fn exn =>
          let
            val exn_msg =
              (case exn of
                STATIC_ERRORS () => ""
              | Runtime.TOPLEVEL_ERROR => ""
              | _ => "Exception- " ^ Pretty.string_of (Runtime.pretty_exn exn) ^ " raised");
            val _ = err exn_msg;
          in expose_error true end);
  in expose_error (#verbose flags) end;

end;
