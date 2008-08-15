(*  Title:      Pure/ML/ml_context.ML
    ID:         $Id$
    Author:     Makarius

ML context and antiquotations.
*)

signature BASIC_ML_CONTEXT =
sig
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
  type antiq =
    {struct_name: string, background: Proof.context} ->
      (Proof.context -> string * string) * Proof.context
  val add_antiq: string ->
    (Position.T -> Context.generic * Args.T list -> antiq * (Context.generic * Args.T list)) -> unit
  val trace: bool ref
  val eval_wrapper: (string -> unit) * (string -> 'a) -> bool -> Position.T -> string -> unit
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

val stored_thms: thm list ref = ref [];

fun ml_store sel (name, ths) =
  let
    val ths' = Context.>>> (Context.map_theory_result (PureThy.store_thms (name, ths)));
    val _ =
      if name = "" then ()
      else if not (ML_Syntax.is_identifier name) then
        error ("Cannot bind theorem(s) " ^ quote name ^ " as ML value")
      else setmp stored_thms ths' (fn () =>
        use_text (0, "") Output.ml_output true
          ("val " ^ name ^ " = " ^ sel ^ "(! ML_Context.stored_thms);")) ();
  in () end;

val ml_store_thms = ml_store "";
fun ml_store_thm (name, th) = ml_store "hd" (name, [th]);

fun bind_thm (name, thm) = ml_store_thm (name, Drule.standard thm);
fun bind_thms (name, thms) = ml_store_thms (name, map Drule.standard thms);

fun thm name = ProofContext.get_thm (the_local_context ()) name;
fun thms name = ProofContext.get_thms (the_local_context ()) name;



(** ML antiquotations **)

(* antiquotation commands *)

type antiq =
  {struct_name: string, background: Proof.context} ->
    (Proof.context -> string * string) * Proof.context;

local

val global_parsers = ref (Symtab.empty:
  (Position.T -> Context.generic * Args.T list -> antiq * (Context.generic * Args.T list))
    Symtab.table);

in

fun add_antiq name scan = CRITICAL (fn () =>
  change global_parsers (fn tab =>
   (if not (Symtab.defined tab name) then ()
    else warning ("Redefined ML antiquotation: " ^ quote name);
    Symtab.update (name, scan) tab)));

fun antiquotation src ctxt =
  let val ((name, _), pos) = Args.dest_src src in
    (case Symtab.lookup (! global_parsers) name of
      NONE => error ("Unknown ML antiquotation command: " ^ quote name ^ Position.str_of pos)
    | SOME scan => (Position.report (Markup.ML_antiq name) pos;
        Args.context_syntax "ML antiquotation" (scan pos) src ctxt))
  end;

end;


(* parsing and evaluation *)

local

structure P = OuterParse;

val antiq =
  P.!!! (P.position P.xname -- Args.parse --| Scan.ahead P.eof)
  >> (fn ((x, pos), y) => Args.src ((x, y), pos));

fun eval_antiquotes struct_name (txt, pos) opt_ctxt =
  let
    val syms = SymbolPos.explode (txt, pos);
    val ants = Antiquote.read (syms, pos);
    val ((ml_env, ml_body), opt_ctxt') =
      if not (exists Antiquote.is_antiq ants)
      then (("", Symbol.escape (SymbolPos.content syms)), opt_ctxt)
      else
        let
          val ctxt =
            (case opt_ctxt of
              NONE => error ("Unknown context -- cannot expand ML antiquotations" ^
                Position.str_of pos)
            | SOME context => Context.proof_of context);

          val lex = #1 (OuterKeyword.get_lexicons ());
          fun no_decl _ = ("", "");

          fun expand (Antiquote.Text s) state = (K ("", Symbol.escape s), state)
            | expand (Antiquote.Antiq x) (scope, background) =
                let
                  val context = Stack.top scope;
                  val (f, context') = antiquotation (Antiquote.read_antiq lex antiq x) context;
                  val (decl, background') = f {background = background, struct_name = struct_name};
                in (decl, (Stack.map_top (K context') scope, background')) end
            | expand (Antiquote.Open _) (scope, background) =
                (no_decl, (Stack.push scope, background))
            | expand (Antiquote.Close _) (scope, background) =
                (no_decl, (Stack.pop scope, background));

          val (decls, (_, ctxt')) = fold_map expand ants (Stack.init ctxt, ctxt);
          val ml = decls |> map (fn decl => decl ctxt') |> split_list |> pairself implode;
        in (ml, SOME (Context.Proof ctxt')) end;
  in (("structure " ^ struct_name ^ " =\nstruct\n" ^ ml_env ^ "end;", ml_body), opt_ctxt') end;

in

val trace = ref false;

fun eval_wrapper pr verbose pos txt =
  let
    val _ = Position.report Markup.ML_source pos;
    val struct_name =
      if Multithreading.available then "Isabelle" ^ serial_string ()
      else "Isabelle";
    val ((env, body), env_ctxt) = eval_antiquotes struct_name (txt, pos) (Context.thread_data ());
    val _ = if ! trace then tracing (cat_lines [env, body]) else ();
    fun eval_raw p =
      use_text (the_default 1 (Position.line_of p), the_default "ML" (Position.file_of p)) pr;
  in
    Context.setmp_thread_data env_ctxt (fn () => eval_raw Position.none false env) ();
    NAMED_CRITICAL "ML" (fn () => eval_raw pos verbose body); (* FIXME non-critical with local ML env *)
    forget_structure struct_name
  end;

end;


(* ML evaluation *)

val eval = eval_wrapper Output.ml_output;
fun eval_file path = eval true (Path.position path) (File.read path);

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

end;

structure Basic_ML_Context: BASIC_ML_CONTEXT = ML_Context;
open Basic_ML_Context;

