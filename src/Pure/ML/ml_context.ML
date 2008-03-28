(*  Title:      Pure/ML/ml_context.ML
    ID:         $Id$
    Author:     Makarius

ML context and antiquotations.
*)

signature BASIC_ML_CONTEXT =
sig
  val store_thm: string * thm -> thm
  val store_thms: string * thm list -> thm list
  val bind_thm: string * thm -> unit
  val bind_thms: string * thm list -> unit
  val thm: xstring -> thm
  val thms: xstring -> thm list
end

signature ML_CONTEXT =
sig
  include BASIC_ML_CONTEXT
  val the_generic_context: unit -> Context.generic
  val the_global_context: unit -> theory
  val the_local_context: unit -> Proof.context
  val exec: (unit -> unit) -> Context.generic -> Context.generic
  val stored_thms: thm list ref
  val ml_store_thm: string * thm -> unit
  val ml_store_thms: string * thm list -> unit
  val add_keywords: string list -> unit
  val inline_antiq: string ->
    (Context.generic * Args.T list -> string * (Context.generic * Args.T list)) -> unit
  val value_antiq: string ->
    (Context.generic * Args.T list -> (string * string) * (Context.generic * Args.T list)) -> unit
  val proj_value_antiq: string -> (Context.generic * Args.T list ->
      (string * string * string) * (Context.generic * Args.T list)) -> unit
  val eval_antiquotes_fn: (string -> string * Position.T -> string * string) ref  (* FIXME tmp *)
  val trace: bool ref
  val eval: bool -> Position.T -> string -> unit
  val eval_file: Path.T -> unit
  val eval_in: Context.generic option -> bool -> Position.T -> string -> unit
  val evaluate: (string -> unit) * (string -> 'b) -> bool ->
    string * (unit -> 'a) option ref -> string -> 'a
  val expression: Position.T -> string -> string -> string -> Context.generic -> Context.generic
end

structure ML_Context: ML_CONTEXT =
struct

(** implicit ML context **)

val the_generic_context = Context.the_thread_data;
val the_global_context = Context.theory_of o the_generic_context;
val the_local_context = Context.proof_of o the_generic_context;

fun exec (e: unit -> unit) context =
  (case Context.setmp_thread_data (SOME context) (fn () => (e (); Context.thread_data ())) () of
    SOME context' => context'
  | NONE => error "Missing context after execution");


(* theorem bindings *)

val store_thms = PureThy.smart_store_thms;
fun store_thm (name, th) = the_single (store_thms (name, [th]));

val stored_thms: thm list ref = ref [];

fun no_ml name =
  if name = "" then true
  else if ML_Syntax.is_identifier name then false
  else error ("Cannot bind theorem(s) " ^ quote name ^ " as ML value");

val use_text_verbose = use_text (0, "") Output.ml_output true;

fun ml_store_thm (name, th) =
  let val th' = store_thm (name, th) in
    if no_ml name then ()
    else setmp stored_thms [th']
      (fn () => use_text_verbose ("val " ^ name ^ " = hd (! ML_Context.stored_thms);")) ()
  end;

fun ml_store_thms (name, ths) =
  let val ths' = store_thms (name, ths) in
    if no_ml name then ()
    else setmp stored_thms ths'
      (fn () => use_text_verbose ("val " ^ name ^ " = ! ML_Context.stored_thms;")) ()
  end;

fun bind_thm (name, thm) = ml_store_thm (name, Drule.standard thm);
fun bind_thms (name, thms) = ml_store_thms (name, map Drule.standard thms);



(** ML antiquotations **)

(* maintain keywords *)

val global_lexicon = ref Scan.empty_lexicon;

fun add_keywords keywords = CRITICAL (fn () =>
  change global_lexicon (Scan.extend_lexicon (map Symbol.explode keywords)));


(* maintain commands *)

datatype antiq = Inline of string | ProjValue of string * string * string;
val global_parsers = ref (Symtab.empty:
  (Context.generic * Args.T list -> antiq * (Context.generic * Args.T list)) Symtab.table);

local

fun add_item kind name scan = CRITICAL (fn () =>
  change global_parsers (fn tab =>
   (if not (Symtab.defined tab name) then ()
    else warning ("Redefined ML antiquotation: " ^ quote name);
    Symtab.update (name, scan >> kind) tab)));

in

val inline_antiq = add_item Inline;
val proj_value_antiq = add_item ProjValue;
fun value_antiq name scan = proj_value_antiq name (scan >> (fn (a, s) => (a, s, "")));

end;


(* command syntax *)

fun syntax scan src =
  #1 (Args.context_syntax "ML antiquotation" scan src (the_local_context ()));

fun command src =
  let val ((name, _), pos) = Args.dest_src src in
    (case Symtab.lookup (! global_parsers) name of
      NONE => error ("Unknown ML antiquotation command: " ^ quote name ^ Position.str_of pos)
    | SOME scan => syntax scan src)
  end;


(* outer syntax *)

structure T = OuterLex;
structure P = OuterParse;

val antiq =
  P.!!! (P.position P.xname -- P.arguments --| Scan.ahead P.eof)
  >> (fn ((x, pos), y) => Args.src ((x, y), pos));


(* input/output wrappers *)

local

fun eval_antiquotes struct_name txt_pos =
  let
    val lex = ! global_lexicon;
    val ants = Antiquote.scan_antiquotes txt_pos;

    fun expand (Antiquote.Text s) names = (("", Symbol.escape s), names)
      | expand (Antiquote.Antiq x) names =
          (case command (Antiquote.scan_arguments lex antiq x) of
            Inline s => (("", s), names)
          | ProjValue (a, s, f) =>
              let
                val a' = if ML_Syntax.is_identifier a then a else "val";
                val ([b], names') = Name.variants [a'] names;
                val binding = "val " ^ b ^ " = " ^ s ^ ";\n";
                val value =
                  if f = "" then struct_name ^ "." ^ b
                  else "(" ^ f ^ " " ^ struct_name ^ "." ^ b ^ ")";
              in ((binding, value), names') end);

    val (decls, body) =
      fold_map expand ants ML_Syntax.reserved
      |> #1 |> split_list |> pairself implode;
  in ("structure " ^ struct_name ^ " =\nstruct\n" ^ decls ^ "end;", body) end;

in

val eval_antiquotes_fn = ref eval_antiquotes;

val trace = ref false;

fun eval_wrapper pr verbose pos txt =
  let
    val struct_name =
      if Multithreading.available then "Isabelle" ^ serial_string ()
      else "Isabelle";
    val (txt1, txt2) = ! eval_antiquotes_fn struct_name (txt, pos);  (* FIXME tmp hook *)
    val _ = if ! trace then tracing (cat_lines [txt1, txt2]) else ();
    fun eval p =
      use_text (the_default 1 (Position.line_of p), the_default "ML" (Position.file_of p)) pr;
  in
    eval Position.none false txt1;
    eval pos verbose txt2;
    forget_structure struct_name
  end;

end;


(* ML evaluation *)

val eval = eval_wrapper Output.ml_output;
fun eval_file path = eval true (Position.path path) (File.read path);

fun eval_in context verbose pos txt =
  Context.setmp_thread_data context (fn () => eval verbose pos txt) ();

fun evaluate pr verbose (ref_name, r) txt = NAMED_CRITICAL "ML" (fn () =>
  let
    val _ = r := NONE;
    val _ = eval_wrapper pr verbose Position.none
      ("val _ = (" ^ ref_name ^ " := SOME (fn () => " ^ txt ^ "))");
  in (case ! r of NONE => error ("Bad evaluation for " ^ ref_name) | SOME e => e) end) ();

fun expression pos bind body txt =
  exec (fn () => eval false pos
    ("Context.set_thread_data (SOME (let " ^ bind ^ " = " ^ txt ^ " in " ^ body ^
      " end (ML_Context.the_generic_context ())));"));


(* basic antiquotations *)

fun context x = (Scan.state >> Context.proof_of) x;

local

val _ = value_antiq "context" (Scan.succeed ("context", "ML_Context.the_local_context ()"));

val _ = inline_antiq "sort" (context -- Scan.lift Args.name >> (fn (ctxt, s) =>
  ML_Syntax.atomic (ML_Syntax.print_sort (Syntax.read_sort ctxt s))));

val _ = inline_antiq "typ" (Args.typ >> (ML_Syntax.atomic o ML_Syntax.print_typ));
val _ = inline_antiq "term" (Args.term >> (ML_Syntax.atomic o ML_Syntax.print_term));
val _ = inline_antiq "prop" (Args.prop >> (ML_Syntax.atomic o ML_Syntax.print_term));

val _ = value_antiq "ctyp" (Args.typ >> (fn T =>
  ("ctyp",
    "Thm.ctyp_of (ML_Context.the_global_context ()) " ^ ML_Syntax.atomic (ML_Syntax.print_typ T))));

val _ = value_antiq "cterm" (Args.term >> (fn t =>
  ("cterm",
    "Thm.cterm_of (ML_Context.the_global_context ()) " ^ ML_Syntax.atomic (ML_Syntax.print_term t))));

val _ = value_antiq "cprop" (Args.prop >> (fn t =>
  ("cprop",
    "Thm.cterm_of (ML_Context.the_global_context ()) " ^ ML_Syntax.atomic (ML_Syntax.print_term t))));

fun type_ syn = (context -- Scan.lift Args.name >> (fn (ctxt, c) =>
    #1 (Term.dest_Type (ProofContext.read_tyname ctxt c))
    |> syn ? Sign.base_name
    |> ML_Syntax.print_string));

val _ = inline_antiq "type_name" (type_ false);
val _ = inline_antiq "type_syntax" (type_ true);

fun const syn = context -- Scan.lift Args.name >> (fn (ctxt, c) =>
  #1 (Term.dest_Const (ProofContext.read_const_proper ctxt c))
  |> syn ? ProofContext.const_syntax_name ctxt
  |> ML_Syntax.print_string);

val _ = inline_antiq "const_name" (const false);
val _ = inline_antiq "const_syntax" (const true);

val _ = inline_antiq "const"
  (context -- Scan.lift Args.name --
    Scan.optional (Scan.lift (Args.$$$ "(") |-- Args.enum1 "," Args.typ --| Scan.lift (Args.$$$ ")")) []
    >> (fn ((ctxt, c), Ts) =>
      let val (c, _) = Term.dest_Const (ProofContext.read_const_proper ctxt c)
      in ML_Syntax.atomic (ML_Syntax.print_term (ProofContext.mk_const ctxt (c, Ts))) end));

in val _ = () end;



(** fact references **)

fun thm name = ProofContext.get_thm (the_local_context ()) name;
fun thms name = ProofContext.get_thms (the_local_context ()) name;


local

fun print_interval (Facts.FromTo arg) =
      "Facts.FromTo " ^ ML_Syntax.print_pair ML_Syntax.print_int ML_Syntax.print_int arg
  | print_interval (Facts.From i) = "Facts.From " ^ ML_Syntax.print_int i
  | print_interval (Facts.Single i) = "Facts.Single " ^ ML_Syntax.print_int i;

fun thm_antiq kind get get_name = value_antiq kind
  (context -- Scan.lift (Args.position Args.name -- Scan.option Args.thm_sel)
  >> (fn (ctxt, ((name, pos), sel)) =>
      let
        val _ = get ctxt (Facts.Named ((name, pos), sel));
        val txt =
          "(Facts.Named ((" ^ ML_Syntax.print_string name ^ ", Position.none), " ^
            ML_Syntax.print_option (ML_Syntax.print_list print_interval) sel ^ "))";
      in (name, get_name ^ " (ML_Context.the_local_context ()) " ^ txt) end));

in

val _ = add_keywords ["(", ")", "-", ","];
val _ = thm_antiq "thm" ProofContext.get_fact_single "ProofContext.get_fact_single";
val _ = thm_antiq "thms" ProofContext.get_fact "ProofContext.get_fact";

end;

val _ = proj_value_antiq "cpat" (Scan.lift Args.name >>
    (fn name => ("cpat",
      "Thm.cterm_of (ML_Context.the_global_context ()) (Syntax.read_term \
      \(ProofContext.set_mode ProofContext.mode_pattern (ML_Context.the_local_context ()))"
      ^ ML_Syntax.print_string name ^ ")", "")));

end;

structure Basic_ML_Context: BASIC_ML_CONTEXT = ML_Context;
open Basic_ML_Context;
