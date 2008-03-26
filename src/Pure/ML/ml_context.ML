(*  Title:      Pure/ML/ml_context.ML
    ID:         $Id$
    Author:     Makarius

ML context and antiquotations.
*)

signature BASIC_ML_CONTEXT =
sig
  val the_context: unit -> theory
  val thm: xstring -> thm
  val thms: xstring -> thm list
end

signature ML_CONTEXT =
sig
  include BASIC_ML_CONTEXT
  val get_context: unit -> Context.generic option
  val set_context: Context.generic option -> unit
  val setmp: Context.generic option -> ('a -> 'b) -> 'a -> 'b
  val the_generic_context: unit -> Context.generic
  val the_local_context: unit -> Proof.context
  val pass_context: Context.generic -> ('a -> 'b) -> 'a -> 'b * Context.generic
  val >> : (theory -> theory) -> unit
  val add_keywords: string list -> unit
  val inline_antiq: string ->
    (Context.generic * Args.T list -> string * (Context.generic * Args.T list)) -> unit
  val value_antiq: string ->
    (Context.generic * Args.T list -> (string * string) * (Context.generic * Args.T list)) -> unit
  val proj_value_antiq: string -> (Context.generic * Args.T list ->
      (string * string * string) * (Context.generic * Args.T list)) -> unit
  val eval_antiquotes_fn: (string * Position.T -> string * string) ref  (* FIXME tmp *)
  val trace: bool ref
  val use_mltext: bool -> Position.T -> string -> Context.generic option -> unit
  val use_mltext_update: bool -> Position.T -> string -> Context.generic -> Context.generic
  val use_let: Position.T -> string -> string -> string -> Context.generic -> Context.generic
  val use: Path.T -> unit
  val evaluate: (string -> unit) * (string -> 'b) -> bool ->
    string * (unit -> 'a) option ref -> string -> 'a
end

structure ML_Context: ML_CONTEXT =
struct

(** Implicit ML context **)

local
  val current_context = ref (NONE: Context.generic option);
in
  fun get_context () = ! current_context;
  fun set_context opt_context = current_context := opt_context;
  fun setmp opt_context f x = Library.setmp current_context opt_context f x;
end;

fun the_generic_context () =
  (case get_context () of
    SOME context => context
  | _ => error "Unknown context");

val the_local_context = Context.proof_of o the_generic_context;

val the_context = Context.theory_of o the_generic_context;

fun pass_context context f x =
  (case setmp (SOME context) (fn () => (f x, get_context ())) () of
    (y, SOME context') => (y, context')
  | (_, NONE) => error "Lost context in ML");

fun change_theory f = NAMED_CRITICAL "ML" (fn () =>
  set_context (SOME (Context.map_theory f (the_generic_context ()))));



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

val isabelle_struct = enclose "structure Isabelle =\nstruct\n" "end;";
val isabelle_struct0 = isabelle_struct "";

fun eval_antiquotes txt_pos =
  let
    val ants = Antiquote.scan_antiquotes txt_pos;

    fun expand (Antiquote.Text s) names = (("", Symbol.escape s), names)
      | expand (Antiquote.Antiq x) names =
          (case command (Antiquote.scan_arguments (! global_lexicon) antiq x) of
            Inline s => (("", s), names)
          | ProjValue (a, s, f) =>
              let
                val a' = if ML_Syntax.is_identifier a then a else "val";
                val ([b], names') = Name.variants [a'] names;
                val binding = "val " ^ b ^ " = " ^ s ^ ";\n";
                val value =
                  if f = "" then "Isabelle." ^ b
                  else "(" ^ f ^ " Isabelle." ^ b ^ ")";
              in ((binding, value), names') end);

    val (decls, body) =
      NAMED_CRITICAL "ML" (fn () => fold_map expand ants ML_Syntax.reserved)
      |> #1 |> split_list |> pairself implode;
  in (isabelle_struct decls, body) end;

in

val eval_antiquotes_fn = ref eval_antiquotes;

val trace = ref false;

fun eval_wrapper pr verbose pos txt =
  let
    val (txt1, txt2) = ! eval_antiquotes_fn (txt, pos);  (* FIXME tmp hook *)
    val _ = if ! trace then tracing (cat_lines [txt1, txt2]) else ();
    fun eval p =
      use_text (the_default 1 (Position.line_of p), the_default "ML" (Position.file_of p)) pr;
  in
    NAMED_CRITICAL "ML" (fn () =>
     (eval Position.none false txt1;
      eval pos verbose txt2;
      eval Position.none false isabelle_struct0))
  end;

end;


(* ML evaluation *)

fun use_mltext verbose pos txt opt_context =
  setmp opt_context (fn () => eval_wrapper Output.ml_output verbose pos txt) ();

fun use_mltext_update verbose pos txt context =
  #2 (pass_context context (fn () => eval_wrapper Output.ml_output verbose pos txt) ());

fun use_let pos bind body txt =
  use_mltext_update false pos
    ("ML_Context.set_context (SOME (let " ^ bind ^ " = " ^ txt ^ " in " ^ body ^
      " end (ML_Context.the_generic_context ())));");

fun use path = eval_wrapper Output.ml_output true (Position.path path) (File.read path);

fun evaluate pr verbose (ref_name, r) txt = NAMED_CRITICAL "ML" (fn () =>
  let
    val _ = r := NONE;
    val _ = eval_wrapper pr verbose Position.none
      ("val _ = (" ^ ref_name ^ " := SOME (fn () => " ^ txt ^ "))");
  in (case ! r of NONE => error ("Bad evaluation for " ^ ref_name) | SOME e => e) end) ();


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
    "Thm.ctyp_of (ML_Context.the_context ()) " ^ ML_Syntax.atomic (ML_Syntax.print_typ T))));

val _ = value_antiq "cterm" (Args.term >> (fn t =>
  ("cterm",
    "Thm.cterm_of (ML_Context.the_context ()) " ^ ML_Syntax.atomic (ML_Syntax.print_term t))));

val _ = value_antiq "cprop" (Args.prop >> (fn t =>
  ("cprop",
    "Thm.cterm_of (ML_Context.the_context ()) " ^ ML_Syntax.atomic (ML_Syntax.print_term t))));

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
      let
        val (c, _) = Term.dest_Const (ProofContext.read_const_proper ctxt c);
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
      "Thm.cterm_of (ML_Context.the_context ()) (Syntax.read_term \
      \(ProofContext.set_mode ProofContext.mode_pattern (ML_Context.the_local_context ()))"
      ^ ML_Syntax.print_string name ^ ")", "")));

(*final declarations of this structure!*)
nonfix >>;
fun >> f = change_theory f;

end;

structure Basic_ML_Context: BASIC_ML_CONTEXT = ML_Context;
open Basic_ML_Context;
