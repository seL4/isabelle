(*  Title:      Pure/Thy/ml_context.ML
    ID:         $Id$
    Author:     Makarius

ML context and antiquotations.
*)

signature BASIC_ML_CONTEXT =
sig
  val the_context: unit -> theory
  val thm: xstring -> thm
  val thms: xstring -> thm list
end;

signature ML_CONTEXT =
sig
  include BASIC_ML_CONTEXT
  val get_context: unit -> Context.generic option
  val set_context: Context.generic option -> unit
  val setmp: Context.generic option -> ('a -> 'b) -> 'a -> 'b
  val the_generic_context: unit -> Context.generic
  val the_local_context: unit -> Proof.context
  val pass: Context.generic option -> ('a -> 'b) -> 'a -> 'b * Context.generic option
  val pass_context: Context.generic -> ('a -> 'b) -> 'a -> 'b * Context.generic
  val save: ('a -> 'b) -> 'a -> 'b
  val >> : (theory -> theory) -> unit
  val add_keywords: string list -> unit
  val inline_antiq: string ->
    (Context.generic * Args.T list -> string * (Context.generic * Args.T list)) -> unit
  val value_antiq: string ->
    (Context.generic * Args.T list -> (string * string) * (Context.generic * Args.T list)) -> unit
  val proj_value_antiq: string -> (Context.generic * Args.T list ->
      (string * string * string) * (Context.generic * Args.T list)) -> unit
  val use_mltext: string -> bool -> Context.generic option -> unit
  val use_mltext_update: string -> bool -> Context.generic -> Context.generic
  val use_let: string -> string -> string -> Context.generic -> Context.generic
  val use: Path.T -> unit
end;

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

fun pass opt_context f x =
  setmp opt_context (fn x => let val y = f x in (y, get_context ()) end) x;

fun pass_context context f x =
  (case pass (SOME context) f x of
    (y, SOME context') => (y, context')
  | (_, NONE) => error "Lost context in ML");

fun save f x = setmp (get_context ()) f x;

fun change_theory f =
  set_context (SOME (Context.map_theory f (the_generic_context ())));


(** ML antiquotations **)

(* maintain keywords *)

val global_lexicon = ref Scan.empty_lexicon;

fun add_keywords keywords =
  change global_lexicon (Scan.extend_lexicon (map Symbol.explode keywords));


(* maintain commands *)

datatype antiq = Inline of string | ProjValue of string * string * string;
val global_parsers = ref (Symtab.empty:
  (Context.generic * Args.T list -> antiq * (Context.generic * Args.T list)) Symtab.table);

local

fun add_item kind name scan = change global_parsers (fn tab =>
 (if not (Symtab.defined tab name) then ()
  else warning ("Redefined ML antiquotation: " ^ quote name);
  Symtab.update (name, scan >> kind) tab));

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
    | SOME scan => transform_failure (curry Antiquote.ANTIQUOTE_FAIL (name, pos))
        (fn () => syntax scan src) ())
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

fun eval_antiquotes txt =
  let
    val ants = Antiquote.scan_antiquotes (txt, Position.line 1);

    fun expand (Antiquote.Text s) names = (("", Symbol.escape s), names)
      | expand (Antiquote.Antiq x) names =
          (case command (Antiquote.scan_arguments (! global_lexicon) antiq x) of
            Inline s => (("", s), names)
          | ProjValue (a, s, f) =>
              let
                val a' = if ML_Syntax.is_identifier a then a else "val";
                val ([b], names') = Name.variants [a'] names;
              in (("val " ^ b ^ " = " ^ s ^ ";\n", f ^ " Isabelle." ^ b), names') end);

    val (decls, body) =
      fold_map expand ants ML_Syntax.reserved
      |> #1 |> split_list |> pairself implode;
  in (isabelle_struct decls, body) end;

fun eval name verbose txt =
  Output.ML_errors (use_text name Output.ml_output verbose) txt;

in

fun eval_wrapper name verbose txt =
  let
    val (txt1, txt2) = eval_antiquotes txt;
    val _ =
      if txt1 = isabelle_struct0 andalso txt2 = txt then ()
      else Output.debug (fn () => cat_lines [txt1, txt2]);
  in eval "" false txt1; eval name verbose txt2; eval "" false isabelle_struct0 end;

end;


(* ML evaluation *)

fun use_mltext txt verbose opt_context =
  setmp opt_context (fn () => eval_wrapper "ML" verbose txt) ();

fun use_mltext_update txt verbose context =
  #2 (pass_context context (eval_wrapper "ML" verbose) txt);

fun use_context txt = use_mltext_update
  ("ML_Context.set_context (SOME ((" ^ txt ^ ") (ML_Context.the_generic_context ())));") false;

fun use_let bind body txt =
  use_context ("let " ^ bind ^ " = " ^ txt ^ " in\n" ^ body ^ " end");

fun use path = eval_wrapper (Path.implode path) true (File.read path);


(* basic antiquotations *)

val _ = value_antiq "context" (Scan.succeed ("context", "ML_Context.the_local_context ()"));

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


fun const syn = (Scan.state >> Context.proof_of) -- Scan.lift Args.name >> (fn (ctxt, c) =>
  #1 (Term.dest_Const (Consts.read_const (ProofContext.consts_of ctxt) c))
  |> syn ? ProofContext.const_syntax_name ctxt
  |> ML_Syntax.print_string);

val _ = inline_antiq "const_name" (const false);
val _ = inline_antiq "const_syntax" (const true);



(** fact references **)

fun thm name = ProofContext.get_thm (the_local_context ()) (Name name);
fun thms name = ProofContext.get_thms (the_local_context ()) (Name name);


local

fun print_interval (FromTo arg) =
      "PureThy.FromTo " ^ ML_Syntax.print_pair ML_Syntax.print_int ML_Syntax.print_int arg
  | print_interval (From i) = "PureThy.From " ^ ML_Syntax.print_int i
  | print_interval (Single i) = "PureThy.Single " ^ ML_Syntax.print_int i;

fun thm_sel name =
  Args.thm_sel >> (fn is => "PureThy.NameSelection " ^
    ML_Syntax.print_pair ML_Syntax.print_string (ML_Syntax.print_list print_interval) (name, is))
  || Scan.succeed ("PureThy.Name " ^ ML_Syntax.print_string name);

fun thm_antiq kind = value_antiq kind
  (Scan.lift (Args.name :-- thm_sel) >> apsnd (fn sel =>
    "ProofContext.get_" ^ kind ^ " (ML_Context.the_local_context ()) " ^ ML_Syntax.atomic sel));

in

val _ = add_keywords ["(", ")", "-", ","];
val _ = thm_antiq "thm";
val _ = thm_antiq "thms";

end;


(*final declarations of this structure!*)
nonfix >>;
fun >> f = change_theory f;

end;

structure Basic_ML_Context: BASIC_ML_CONTEXT = ML_Context;
open Basic_ML_Context;
