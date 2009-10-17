(*  Title:      Pure/ML/ml_context.ML
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
  val stored_thms: thm list Unsynchronized.ref
  val ml_store_thm: string * thm -> unit
  val ml_store_thms: string * thm list -> unit
  type antiq =
    {struct_name: string, background: Proof.context} ->
      (Proof.context -> string * string) * Proof.context
  val add_antiq: string -> (Position.T -> antiq context_parser) -> unit
  val trace: bool Unsynchronized.ref
  val eval_antiquotes: ML_Lex.token Antiquote.antiquote list * Position.T ->
    Context.generic option -> (ML_Lex.token list * ML_Lex.token list) * Context.generic option
  val eval: bool -> Position.T -> Symbol_Pos.text -> unit
  val eval_file: Path.T -> unit
  val eval_in: Proof.context option -> bool -> Position.T -> Symbol_Pos.text -> unit
  val evaluate: Proof.context -> bool ->
    string * (unit -> 'a) option Unsynchronized.ref -> string -> 'a
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

val stored_thms: thm list Unsynchronized.ref = Unsynchronized.ref [];

fun ml_store sel (name, ths) =
  let
    val ths' = Context.>>> (Context.map_theory_result
      (PureThy.store_thms (Binding.name name, ths)));
    val _ =
      if name = "" then ()
      else if not (ML_Syntax.is_identifier name) then
        error ("Cannot bind theorem(s) " ^ quote name ^ " as ML value")
      else setmp_CRITICAL stored_thms ths' (fn () =>
        ML_Compiler.eval true Position.none
          (ML_Lex.tokenize ("val " ^ name ^ " = " ^ sel ^ "(! ML_Context.stored_thms);"))) ();
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

val global_parsers =
  Unsynchronized.ref (Symtab.empty: (Position.T -> antiq context_parser) Symtab.table);

in

fun add_antiq name scan = CRITICAL (fn () =>
  Unsynchronized.change global_parsers (fn tab =>
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
structure T = OuterLex;

val antiq =
  P.!!! (P.position P.xname -- Args.parse --| Scan.ahead P.eof)
  >> (fn ((x, pos), y) => Args.src ((x, y), pos));

val struct_name = "Isabelle";
val begin_env = ML_Lex.tokenize ("structure " ^ struct_name ^ " =\nstruct\n");
val end_env = ML_Lex.tokenize "end;";
val reset_env = ML_Lex.tokenize "structure Isabelle = struct end";

in

fun eval_antiquotes (ants, pos) opt_context =
  let
    val opt_ctxt = Option.map (Context.Proof o Context.proof_of) opt_context;
    val ((ml_env, ml_body), opt_ctxt') =
      if forall Antiquote.is_text ants
      then (([], map (fn Antiquote.Text tok => tok) ants), opt_ctxt)
      else
        let
          val ctxt =
            (case opt_ctxt of
              NONE => error ("No context -- cannot expand ML antiquotations" ^ Position.str_of pos)
            | SOME ctxt => Context.proof_of ctxt);

          val lex = #1 (OuterKeyword.get_lexicons ());
          fun no_decl _ = ([], []);

          fun expand (Antiquote.Text tok) state = (K ([], [tok]), state)
            | expand (Antiquote.Antiq (ss, range)) (scope, background) =
                let
                  val context = Stack.top scope;
                  val (f, context') = antiquotation (T.read_antiq lex antiq (ss, #1 range)) context;
                  val (decl, background') = f {background = background, struct_name = struct_name};
                  val decl' = decl #> pairself (ML_Lex.tokenize #> map (ML_Lex.set_range range));
                in (decl', (Stack.map_top (K context') scope, background')) end
            | expand (Antiquote.Open _) (scope, background) =
                (no_decl, (Stack.push scope, background))
            | expand (Antiquote.Close _) (scope, background) =
                (no_decl, (Stack.pop scope, background));

          val (decls, (_, ctxt')) = fold_map expand ants (Stack.init ctxt, ctxt);
          val ml = decls |> map (fn decl => decl ctxt') |> split_list |> pairself flat;
        in (ml, SOME (Context.Proof ctxt')) end;
  in ((begin_env @ ml_env @ end_env, ml_body), opt_ctxt') end;

val trace = Unsynchronized.ref false;

fun eval verbose pos txt =
  let
    (*prepare source text*)
    val _ = Position.report Markup.ML_source pos;
    val ants = ML_Lex.read_antiq (Symbol_Pos.explode (txt, pos), pos);
    val ((env, body), env_ctxt) = eval_antiquotes (ants, pos) (Context.thread_data ());
    val _ =
      if ! trace then tracing (cat_lines [ML_Lex.flatten env, ML_Lex.flatten body])
      else ();

    (*prepare static ML environment*)
    val _ = Context.setmp_thread_data env_ctxt
        (fn () => (ML_Compiler.eval false Position.none env; Context.thread_data ())) ()
      |> (fn NONE => () | SOME context' => Context.>> (ML_Env.inherit context'));

    val _ = ML_Compiler.eval verbose pos body;
    val _ = ML_Compiler.eval false Position.none reset_env;
  in () end;

end;


(* derived versions *)

fun eval_file path = eval true (Path.position path) (File.read path);

fun eval_in ctxt verbose pos txt =
  Context.setmp_thread_data (Option.map Context.Proof ctxt) (fn () => eval verbose pos txt) ();

fun evaluate ctxt verbose (ref_name, r) txt = NAMED_CRITICAL "ML" (fn () =>
  let
    val _ = r := NONE;
    val _ = Context.setmp_thread_data (SOME (Context.Proof ctxt)) (fn () =>
      eval verbose Position.none ("val _ = (" ^ ref_name ^ " := SOME (fn () => " ^ txt ^ "))")) ();
  in (case ! r of NONE => error ("Bad evaluation for " ^ ref_name) | SOME e => e) end) ();

fun expression pos bind body txt =
  exec (fn () => eval false pos
    ("Context.set_thread_data (SOME (let " ^ bind ^ " = " ^ txt ^ " in " ^ body ^
      " end (ML_Context.the_generic_context ())));"));

end;

structure Basic_ML_Context: BASIC_ML_CONTEXT = ML_Context;
open Basic_ML_Context;
