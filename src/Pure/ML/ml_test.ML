(*  Title:      Pure/ML/ml_test.ML
    Author:     Makarius

Test of advanced ML compiler invocation in Poly/ML 5.3.
*)

signature ML_TEST =
sig
  val get_result: Proof.context -> PolyML.parseTree list
  val eval: bool -> Position.T -> ML_Lex.token list -> unit
end

structure ML_Test: ML_TEST =
struct

(* eval ML source tokens *)

structure Result = GenericDataFun
(
  type T = PolyML.parseTree list;
  val empty = [];
  fun extend _ = [];
  fun merge _ _ = [];
);

val get_result = Result.get o Context.Proof;


fun use_text ({name_space = space, print, error, ...}: use_context) verbose pos toks =
  let
    (* input *)

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


    (* output *)

    val out_buffer = ref ([]: string list);
    fun output () = implode (rev (! out_buffer));
    fun put s = out_buffer := s :: ! out_buffer;

    fun put_message {message, hard, location, context = _} =
     (put (if hard then "Error: " else "Warning: ");
      put (Pretty.string_of (Pretty.from_ML (pretty_ml message)));
      put (Position.str_of (pos_of location) ^ "\n"));


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

    fun result_fun (parse_tree, code) () =
     (Context.>> (Result.map (append (the_list parse_tree)));
      (case code of NONE => warning "Static Errors" | SOME result => apply_result (result ())));


    (* compiler invocation *)

    val parameters =
     [PolyML.Compiler.CPOutStream put,
      PolyML.Compiler.CPNameSpace space,
      PolyML.Compiler.CPErrorMessageProc put_message,
      PolyML.Compiler.CPLineNo (fn () => ! current_line),
      PolyML.Compiler.CPLineOffset get_index,
      PolyML.Compiler.CPFileName (the_default "ML" (Position.file_of pos)),
      PolyML.Compiler.CPPrintInAlphabeticalOrder false,
      PolyML.Compiler.CPCompilerResultFun result_fun];
    val _ =
      (while not (List.null (! in_buffer)) do
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

