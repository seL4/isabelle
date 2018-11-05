(*  Title:      Tools/Haskell/Test.thy
    Author:     Makarius
*)

section \<open>Test build of Isabelle/Haskell modules\<close>

theory Test imports Haskell
begin

ML \<open>
  Isabelle_System.with_tmp_dir "ghc" (fn dir =>
    let
      val _ = Haskell.install_sources dir;
      val (out, rc) =
        Isabelle_System.bash_output
         (cat_lines
           ["set -e",
            "cd " ^ File.bash_path dir,
            "\"$ISABELLE_GHC\" " ^ File.bash_paths Haskell.sources]);
    in if rc = 0 then writeln out else error out end)
\<close>

end
