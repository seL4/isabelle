(*  Title:      Tools/Haskell/Haskell.thy
    Author:     Makarius
*)

section \<open>Support for Isabelle tool development in Haskell\<close>

theory Haskell
  imports Pure
  keywords "generate_haskell_file" "export_haskell_file" :: thy_decl
begin

ML \<open>
  Outer_Syntax.command \<^command_keyword>\<open>generate_haskell_file\<close> "generate Haskell file"
    (Parse.position Parse.path -- (\<^keyword>\<open>=\<close> |-- Parse.input Parse.embedded) >>
      (fn (file, source) =>
        Toplevel.keep (fn state =>
          let
            val ctxt = Toplevel.context_of state;
            val thy = Toplevel.theory_of state;

            val path = Resources.check_path ctxt (Resources.master_directory thy) file;
            val text = GHC.read_source ctxt source;
            val _ = Isabelle_System.mkdirs (Path.dir (Path.expand path));
            val _ = if try File.read path = SOME text then () else File.write path text;
          in () end)));
\<close>

ML \<open>
  Outer_Syntax.command \<^command_keyword>\<open>export_haskell_file\<close> "export Haskell file"
    (Parse.name -- (\<^keyword>\<open>=\<close> |-- Parse.input Parse.embedded) >>
      (fn (name, source) =>
        Toplevel.keep (fn state =>
          let
            val ctxt = Toplevel.context_of state;
            val thy = Toplevel.theory_of state;

            val text = GHC.read_source ctxt source;
            val _ = Export.export thy name [text];
          in () end)));
\<close>

end
