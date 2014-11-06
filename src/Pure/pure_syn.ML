(*  Title:      Pure/pure_syn.ML
    Author:     Makarius

Minimal outer syntax for bootstrapping Isabelle/Pure.
*)

structure Pure_Syn: sig end =
struct

(* keywords *)

val keywords: Thy_Header.keywords =
 [("theory", SOME (("thy_begin", []), ["theory"])),
  ("ML_file", SOME (("thy_load", []), ["ML"]))];

fun command_spec (name, pos) =
  (case AList.lookup (op =) keywords name of
    SOME (SOME spec) => Keyword.command_spec ((name, spec), pos)
  | _ => error ("Bad command specification " ^ quote name ^ Position.here pos));

val _ = Thy_Header.define_keywords keywords;
val _ = Theory.setup (fold Thy_Header.declare_keyword keywords);


(* commands *)

val _ =
  Outer_Syntax.command
    (command_spec ("theory", @{here})) "begin theory"
    (Thy_Header.args >>
      (fn _ => Toplevel.init_theory (fn () => error "Missing theory initialization")));

val _ =
  Outer_Syntax.command
    (command_spec ("ML_file", @{here})) "ML text from file"
    (Resources.parse_files "ML_file" >> (fn files => Toplevel.generic_theory (fn gthy =>
        let
          val [{src_path, lines, digest, pos}] = files (Context.theory_of gthy);
          val provide = Resources.provide (src_path, digest);
          val source = {delimited = true, text = cat_lines lines, pos = pos};
          val flags = {SML = false, exchange = false, redirect = true, verbose = true};
        in
          gthy
          |> ML_Context.exec (fn () => ML_Context.eval_source flags source)
          |> Local_Theory.propagate_ml_env
          |> Context.mapping provide (Local_Theory.background_theory provide)
        end)));

end;

