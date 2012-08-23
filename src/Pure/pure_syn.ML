(*  Title:      Pure/pure_syn.ML
    Author:     Makarius

Minimal outer syntax for bootstrapping Pure.
*)

structure Pure_Syn: sig end =
struct

val _ =
  Outer_Syntax.command
    (("theory", Keyword.tag_theory Keyword.thy_begin), Position.none) "begin theory context"
    (Thy_Header.args >> (fn header =>
      Toplevel.print o
        Toplevel.init_theory
          (fn () => Thy_Info.toplevel_begin_theory (Thy_Load.get_master_path ()) header)));

val _ =
  Outer_Syntax.command
    (("ML_file", Keyword.tag_ml Keyword.thy_load), Position.none) "ML text from file"
    (Scan.ahead Parse.path -- Thy_Load.parse_files "ML_file"
      >> (fn (name, files) => Toplevel.generic_theory (fn gthy =>
        let
          val src_path = Path.explode name;
          val (_, [(txt, pos)]) = files (Context.theory_of gthy);
          val provide = Thy_Load.provide (src_path, SHA1.digest txt);
        in
          gthy
          |> ML_Context.exec (fn () => ML_Context.eval_text true pos txt)
          |> Local_Theory.propagate_ml_env
          |> Context.mapping provide (Local_Theory.background_theory provide)
        end)));

end;

