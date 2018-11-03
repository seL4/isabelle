(*  Title:      Tools/Haskell/Build.thy
    Author:     Makarius
*)

section \<open>Build Isabelle/Haskell modules\<close>

theory Build imports Haskell
begin

ML_command \<open>
  Isabelle_System.with_tmp_dir "ghc" (fn dir =>
    let
      val (out, rc) =
        Isabelle_System.bash_output
         (cat_lines
           ["set -e",
            "cd " ^ File.bash_path dir,
            "cp " ^ File.bash_paths Haskell.source_modules ^ " .",
            "\"$ISABELLE_GHC\" " ^ File.bash_paths (map Path.base Haskell.source_modules)]);
    in if rc = 0 then writeln out else error out end
  )
\<close>

end
