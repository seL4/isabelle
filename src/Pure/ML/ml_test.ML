(*  Title:      Pure/ML/ml_test.ML
    Author:     Makarius

Test of advanced ML compiler invocation in Poly/ML 5.3.
*)

signature ML_TEST =
sig
  val eval: bool -> Position.T -> ML_Lex.token list -> unit
end

structure ML_Test: ML_TEST =
struct

(* extra ML environment *)

structure Extra_Env = GenericDataFun
(
  type T = Position.T Inttab.table;  (*position of registered tokens*)
  val empty = Inttab.empty;
  val extend = I;
  fun merge _ = Inttab.merge (K true);
);

fun inherit_env context =
  ML_Context.inherit_env context #>
  Extra_Env.put (Extra_Env.get context);

fun register_tokens toks context =
  let
    val regs = map (fn tok => (serial (), tok)) toks;
    val context' = context
      |> Extra_Env.map (fold (fn (i, tok) => Inttab.update (i, ML_Lex.pos_of tok)) regs);
  in (regs, context') end;

fun pos_of_location context
    ({file, startLine = line, startPosition = i, endPosition = j, ...}: location) =
  (case pairself (Inttab.lookup (Extra_Env.get context)) (i, j) of
    (SOME pos1, SOME pos2) => Position.encode_range (pos1, pos2)
  | (SOME pos, NONE) => pos
  | _ => Position.line_file line file);


(* parse trees *)

fun report_parse_tree context =
  let
    val pos_of = pos_of_location context;
    fun report loc (PTtype types) =  (* FIXME body text *)
          Position.report Markup.ML_typing (pos_of loc)
      | report loc (PTdeclaredAt decl) =
          Markup.markup (Markup.properties (Position.properties_of (pos_of decl)) Markup.ML_def) ""
          |> Position.report_text Markup.ML_ref (pos_of loc)
      | report _ (PTnextSibling tree) = report_tree (tree ())
      | report _ (PTfirstChild tree) = report_tree (tree ())
      | report _ _ = ()
    and report_tree (loc, props) = List.app (report loc) props;
  in report_tree end;


(* eval ML source tokens *)

fun use_text ({name_space = space, print, error, ...}: use_context) verbose pos toks =
  let
    (* input *)

    val input = Context.>>> (register_tokens toks);
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
      put (Position.str_of (pos_of_location (the (Context.thread_data ())) location) ^ "\n"));


    (* results *)

    fun apply_result {fixes, types, signatures, structures, functors, values} =
      let
        fun add_prefix prefix (PrettyBlock (ind, consistent, context, prts)) =
              let
                fun make_prefix context =
                  (case get_first (fn ContextParentStructure p => SOME p | _ => NONE) context of
                    SOME (name, sub_context) => make_prefix sub_context ^ name ^ "."
                  | NONE => prefix);
                val this_prefix = make_prefix context;
              in PrettyBlock (ind, consistent, context, map (add_prefix this_prefix) prts) end
          | add_prefix prefix (prt as PrettyString s) =
              if prefix = "" then prt else PrettyString (prefix ^ s)
          | add_prefix _ (prt as PrettyBreak _) = prt;

        val depth = get_print_depth ();
        val with_struct = ! PolyML.Compiler.printTypesWithStructureName;

        fun display disp x =
          if depth > 0 then
            (disp x
              |> with_struct ? add_prefix ""
              |> pretty_ml |> Pretty.from_ML |> Pretty.string_of |> put; put "\n")
          else ();

        fun apply_fix (a, b) =
          (display PolyML.NameSpace.displayFix (a, b); #enterFix space (a, b));
        fun apply_type (a, b) =
          (display PolyML.NameSpace.displayType (b, depth); #enterType space (a, b));
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
      | SOME parse_tree => report_parse_tree (the (Context.thread_data ())) parse_tree;
      case phase2 of NONE => error "Static Errors"
      | SOME code => apply_result (Toplevel.program code));


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
        error (output ()); raise exn);
  in if verbose then print (output ()) else () end;

val eval = use_text ML_Context.local_context;


(* ML test command *)

fun ML_test (txt, pos) =
  let
    val _ = Position.report Markup.ML_source pos;
    val ants = ML_Lex.read_antiq (Symbol_Pos.explode (txt, pos), pos);
    val ((env, body), env_ctxt) = ML_Context.eval_antiquotes (ants, pos) (Context.thread_data ());

    val _ = Context.setmp_thread_data env_ctxt
        (fn () => (eval false Position.none env; Context.thread_data ())) ()
      |> (fn NONE => () | SOME context' => Context.>> (inherit_env context'));
    val _ = eval true pos body;
    val _ = eval false Position.none (ML_Lex.tokenize "structure Isabelle = struct end");
  in () end;


local structure P = OuterParse and K = OuterKeyword in

fun propagate_env (context as Context.Proof lthy) =
      Context.Proof (LocalTheory.map_contexts (inherit_env context) lthy)
  | propagate_env context = context;

val _ =
  OuterSyntax.command "ML_test" "advanced ML compiler test" (K.tag_ml K.thy_decl)
    (P.ML_source >> (fn src =>
      Toplevel.generic_theory (ML_Context.exec (fn () => ML_test src) #> propagate_env)));

end;

end;

