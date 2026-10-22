(*  Title:      Pure/ML/ml_context.ML
    Author:     Makarius

ML context and antiquotations.
*)

signature ML_CONTEXT =
sig
  val check_antiquotation: Proof.context -> xstring * Position.T -> string
  val struct_name: Proof.context -> string
  val variant: string -> Proof.context -> string * Proof.context
  type decl = Proof.context -> ML_Lex.token list * ML_Lex.token list
  type decls = Proof.context -> (ML_Lex.token list * ML_Lex.token list) list
  type 'a antiquotation = Position.range -> 'a -> Proof.context -> decl * Proof.context
  val add_antiquotation: binding -> bool -> Token.src antiquotation -> theory -> theory
  val add_antiquotation_embedded: binding -> Input.source antiquotation -> theory -> theory
  val print_antiquotations: bool -> Proof.context -> unit
  val expand_antiquotes: ML_Lex.token Antiquote.antiquote list ->
    Proof.context -> decl * Proof.context
  val expand_antiquotes_list: ML_Lex.token Antiquote.antiquote list list ->
    Proof.context -> decls * Proof.context
  val read_antiquotes: Input.source -> Proof.context -> decl * Proof.context
  val eval: ML_Compiler.flags -> Position.T -> ML_Lex.token Antiquote.antiquote list -> unit
  val eval_file: ML_Compiler.flags -> Path.T -> unit
  val eval_source: ML_Compiler.flags -> Input.source -> unit
  val eval_in: Proof.context option -> ML_Compiler.flags -> Position.T ->
    ML_Lex.token Antiquote.antiquote list -> unit
  val eval_source_in: Proof.context option -> ML_Compiler.flags -> Input.source -> unit
  val exec: (unit -> unit) -> Context.generic -> Context.generic
  val expression: Position.T -> ML_Lex.token Antiquote.antiquote list ->
    Context.generic -> Context.generic
end

structure ML_Context: ML_CONTEXT =
struct

(** ML antiquotations **)

(* names for generated environment *)

structure Names = Proof_Data
(
  type T = string * Name.context;
  val init_names = ML_Syntax.reserved |> Name.declare "ML_context";
  fun init _ = ("Isabelle0", init_names);
);

fun struct_name ctxt = #1 (Names.get ctxt);
val struct_begin = (Names.map o apfst) (fn _ => "Isabelle" ^ serial_string ());

fun variant a ctxt =
  let
    val names = #2 (Names.get ctxt);
    val (b, names') = Name.variant (Name.desymbolize (SOME false) a) names;
    val ctxt' = (Names.map o apsnd) (K names') ctxt;
  in (b, ctxt') end;


(* theory data *)

type decl =
  Proof.context -> ML_Lex.token list * ML_Lex.token list;  (*final context -> ML env, ML body*)

type decls = Proof.context -> (ML_Lex.token list * ML_Lex.token list) list;

type 'a antiquotation = Position.range -> 'a -> Proof.context -> decl * Proof.context;

structure Antiquotations = Theory_Data
(
  type T = (bool * Token.src antiquotation) Name_Space.table;
  val empty : T = Name_Space.empty_table Markup.ML_antiquotationN;
  fun merge data : T = Name_Space.merge_tables data;
);

val get_antiquotations = Antiquotations.get o Proof_Context.theory_of;

fun check_antiquotation ctxt =
  #1 o Name_Space.check (Context.Proof ctxt) (get_antiquotations ctxt);

fun add_antiquotation name embedded antiquotation thy =
  thy |> Antiquotations.map
    (Name_Space.define (Context.Theory thy) true (name, (embedded, antiquotation)) #> #2);

fun add_antiquotation_embedded name antiquotation =
  add_antiquotation name true
    (fn range => fn src => fn ctxt =>
      antiquotation range (Token.read ctxt Parse.embedded_input src) ctxt);

fun print_antiquotations verbose ctxt =
  Pretty.big_list "ML antiquotations:"
    (map (Pretty.marks_str o #1) (Name_Space.markups_table verbose ctxt (get_antiquotations ctxt)))
  |> Pretty.writeln;

fun apply_antiquotation range src ctxt =
  let
    val (src', (embedded, antiquotation)) = Token.check_src ctxt get_antiquotations src;
    val _ =
      if Options.default_bool "update_control_cartouches" then
        Context_Position.reports_text ctxt
          (Antiquote.update_reports embedded (#1 range) (map Token.content_of src'))
      else ();
  in antiquotation range src' ctxt end;


(* formality check for string literals *)

local

fun name_space_completions ctxt a (antiq_name, global_space, local_space, read) =
  if can (Name_Space.the_entry global_space) a then
    let val kind = Name_Space.kind_of local_space in
      [Name_Space.extern ctxt local_space a, a]
      |> distinct (op =)
      |> map_filter (fn b =>
          if try read b = SOME a
          then SOME (Antiquote.make_control_antiq antiq_name b, (kind, a))
          else NONE)
    end
  else [];

fun formal_completion ctxt (a, pos) =
  let
    val read_flags = {proper = true, strict = true};
    val read_const = Proof_Context.read_const read_flags ctxt #> dest_Const_name;
    val read_type = Proof_Context.read_type_name read_flags ctxt #> dest_Type_name;

    val thy = Proof_Context.theory_of ctxt;
    val consts = ("const_name", Sign.const_space thy, Proof_Context.const_space ctxt, read_const);
    val types = ("type_name", Sign.type_space thy, Proof_Context.type_space ctxt, read_type);

    val names =
      maps (name_space_completions ctxt a) [consts, types] @
      [(Antiquote.make_control_antiq "unchecked_name" a, (Markup.ML_stringN, a))];
  in Completion.names pos names end;

in

fun check_string context tok =
  if ML_Lex.check_string tok andalso Config.get_generic context ML_Env.ML_check_strings andalso
    String.exists_str (fn "." => true | _ => false) (ML_Lex.content_of tok)
  then
    let
      val ctxt = Context.proof_of context;
      val txt = unenclose (ML_Lex.content_of tok);
      val pos = ML_Lex.pos_of tok;
    in
      if Long_Name.is_identifier txt then
        legacy_feature ("ML string looks like formal name: " ^ quote txt ^
          "\nbetter use antiquotations like \<^const_name>\<open>\<dots>\<close>, \<^type_name>\<open>\<dots>\<close>, \<^unchecked_name>\<open>\<dots>\<close>, \<^verbatim>\<open>\<dots>\<close> etc." ^
          Position.here pos ^ Completion.markup_report [formal_completion ctxt (txt, pos)])
      else ()
    end
  else ();

end;


(* parsing *)

local

val antiq =
  Parse.!!! ((Parse.token Parse.liberal_name ::: Parse.args) --| Scan.ahead Parse.eof);

fun expand_antiquote ant ctxt =
  (case ant of
    Antiquote.Text tok => (check_string (Context.Proof ctxt) tok; (K ([], [tok]), ctxt))
  | Antiquote.Control {name, range, body} =>
      ctxt |> apply_antiquotation range
        (Token.make_src name (if null body then [] else [Token.read_cartouche body]))
  | Antiquote.Antiq {range, body, ...} =>
      ctxt |> apply_antiquotation range
        (Parse.read_antiq (Thy_Header.get_keywords' ctxt) antiq (body, #1 range)));

in

fun expand_antiquotes ants ctxt =
  let
    val (decls, ctxt') = fold_map expand_antiquote ants ctxt;
    fun decl ctxt'' = decls |> map (fn d => d ctxt'') |> split_list |> apply2 flat;
  in (decl, ctxt') end;

fun expand_antiquotes_list antss ctxt =
  let
    val (decls, ctxt') = fold_map expand_antiquotes antss ctxt;
    fun decl' ctxt'' = map (fn decl => decl ctxt'') decls;
  in (decl', ctxt') end

end;

val read_antiquotes = expand_antiquotes o ML_Lex.read_source;


(* evaluation *)

local

fun make_env name visible =
  (ML_Lex.tokenize
    ("structure " ^ name ^ " =\nstruct\n\
     \val ML_context = Context_Position.set_visible " ^ Bool.toString visible ^
     " (Context.the_local_context ());\n"),
   ML_Lex.tokenize "end;");

fun reset_env name = ML_Lex.tokenize ("structure " ^ name ^ " = struct end");

fun no_eval_antiquote opt_context ant =
  let
    val tok = Antiquote.the_text "No context -- cannot expand ML antiquotations" ant;
    val _ =
      (case opt_context of
        NONE => ()
      | SOME context => check_string context tok);
  in tok end;

fun eval_antiquotes ants opt_context =
  if forall Antiquote.is_text ants orelse is_none opt_context then
    (([], map (no_eval_antiquote opt_context) ants), Option.map Context.proof_of opt_context)
  else
    let
      val context = the opt_context;
      val visible =
        (case context of
          Context.Proof ctxt => Context_Position.is_visible ctxt
        | _ => true);
      val ctxt = struct_begin (Context.proof_of context);
      val (begin_env, end_env) = make_env (struct_name ctxt) visible;
      val (decl, ctxt') = expand_antiquotes ants ctxt;
      val (ml_env, ml_body) = decl ctxt';
    in ((begin_env @ ml_env @ end_env, ml_body), SOME ctxt') end;

in

fun eval flags pos ants =
  let
    val non_verbose = ML_Compiler.verbose false flags;

    (*prepare source text*)
    val ((env, body), env_ctxt) = eval_antiquotes ants (Context.get_generic_context ());
    val _ =
      (case env_ctxt of
        SOME ctxt =>
          if Config.get ctxt ML_Options.source_trace andalso Context_Position.is_visible ctxt
          then tracing (cat_lines [ML_Lex.flatten env, ML_Lex.flatten body])
          else ()
      | NONE => ());

    (*prepare environment*)
    val _ =
      Context.setmp_generic_context
        (Option.map (Context.Proof o Context_Position.set_visible false) env_ctxt)
        (fn () =>
          (ML_Compiler.eval non_verbose Position.none env; Context.get_generic_context ())) ()
      |> (fn NONE => () | SOME context' => Context.>> (ML_Env.inherit [context']));

    (*eval body*)
    val _ = ML_Compiler.eval flags pos body;

    (*clear environment*)
    val _ =
      (case (env_ctxt, is_some (Context.get_generic_context ())) of
        (SOME ctxt, true) =>
          let
            val name = struct_name ctxt;
            val _ = ML_Compiler.eval non_verbose Position.none (reset_env name);
            val _ = Context.>> (ML_Env.forget_structure name);
          in () end
      | _ => ());
  in () end;

end;


(* derived versions *)

fun eval_file flags path =
  let val pos = Position.file (File.symbolic_path path)
  in eval flags pos (ML_Lex.read_source_text (File.read path, pos)) end;

fun eval_source flags source =
  let
    val opt_context = Context.get_generic_context ();
    val {read_source, ...} = ML_Env.operations opt_context (#environment flags);
  in eval flags (Input.pos_of source) (read_source source) end;

fun eval_in ctxt flags pos ants =
  Context.setmp_generic_context (Option.map Context.Proof ctxt)
    (fn () => eval flags pos ants) ();

fun eval_source_in ctxt flags source =
  Context.setmp_generic_context (Option.map Context.Proof ctxt)
    (fn () => eval_source flags source) ();

fun exec (e: unit -> unit) context =
  (case Context.setmp_generic_context (SOME context)
      (fn () => (e (); Context.get_generic_context ())) () of
    SOME context' => context'
  | NONE => error "Missing context after execution");

fun expression pos ants =
  Local_Theory.touch_ml_env #>
  exec (fn () => eval ML_Compiler.flags pos ants);

end;

val ML = ML_Context.eval_source (ML_Compiler.verbose true ML_Compiler.flags);
val ML_command = ML_Context.eval_source ML_Compiler.flags;
