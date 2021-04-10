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
  type antiquotation = Position.range -> Token.src -> Proof.context -> decl * Proof.context
  val add_antiquotation: binding -> bool -> antiquotation -> theory -> theory
  val print_antiquotations: bool -> Proof.context -> unit
  val expand_antiquotes: ML_Lex.token Antiquote.antiquote list ->
    Proof.context -> decl * Proof.context
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

type antiquotation =
  Position.range -> Token.src -> Proof.context -> decl * Proof.context;

structure Antiquotations = Theory_Data
(
  type T = (bool * antiquotation) Name_Space.table;
  val empty : T = Name_Space.empty_table Markup.ML_antiquotationN;
  val extend = I;
  fun merge data : T = Name_Space.merge_tables data;
);

val get_antiquotations = Antiquotations.get o Proof_Context.theory_of;

fun check_antiquotation ctxt =
  #1 o Name_Space.check (Context.Proof ctxt) (get_antiquotations ctxt);

fun add_antiquotation name embedded antiquotation thy =
  thy |> Antiquotations.map
    (Name_Space.define (Context.Theory thy) true (name, (embedded, antiquotation)) #> #2);

fun print_antiquotations verbose ctxt =
  Pretty.big_list "ML antiquotations:"
    (map (Pretty.mark_str o #1) (Name_Space.markup_table verbose ctxt (get_antiquotations ctxt)))
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


(* parsing *)

local

val antiq =
  Parse.!!! ((Parse.token Parse.liberal_name ::: Parse.args) --| Scan.ahead Parse.eof);

fun expand_antiquote ant ctxt =
  (case ant of
    Antiquote.Text tok => (K ([], [tok]), ctxt)
  | Antiquote.Control {name, range, body} =>
      ctxt |> apply_antiquotation range
        (Token.make_src name (if null body then [] else [Token.read_cartouche body]))
  | Antiquote.Antiq {range, body, ...} =>
      ctxt |> apply_antiquotation range
        (Token.read_antiq (Thy_Header.get_keywords' ctxt) antiq (body, #1 range)));

in

fun expand_antiquotes ants ctxt =
  let
    val (decls, ctxt') = fold_map expand_antiquote ants ctxt;
    fun decl ctxt'' = decls |> map (fn d => d ctxt'') |> split_list |> apply2 flat;
  in (decl, ctxt') end;

end;


(* evaluation *)

local

fun make_env name visible =
  (ML_Lex.tokenize
    ("structure " ^ name ^ " =\nstruct\n\
     \val ML_context = Context_Position.set_visible " ^ Bool.toString visible ^
     " (Context.the_local_context ());\n"),
   ML_Lex.tokenize "end;");

fun reset_env name = ML_Lex.tokenize ("structure " ^ name ^ " = struct end");

fun eval_antiquotes ants opt_context =
  if forall Antiquote.is_text ants orelse is_none opt_context then
    (([], map (Antiquote.the_text "No context -- cannot expand ML antiquotations") ants),
      Option.map Context.proof_of opt_context)
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
  let val pos = Path.position path
  in eval flags pos (ML_Lex.read_text (File.read path, pos)) end;

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

fun expression pos ants = exec (fn () => eval ML_Compiler.flags pos ants);

end;

val ML = ML_Context.eval_source (ML_Compiler.verbose true ML_Compiler.flags);
