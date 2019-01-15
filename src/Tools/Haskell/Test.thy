(*  Title:      Tools/Haskell/Test.thy
    Author:     Makarius
*)

section \<open>Test build of Isabelle/Haskell modules\<close>

theory Test imports Haskell
begin

ML \<open>
  Isabelle_System.with_tmp_dir "ghc" (fn tmp_dir =>
    let
      val src_dir = Path.append tmp_dir (Path.explode "src");
      val files = Generated_Files.write_files \<^theory>\<open>Haskell\<close> src_dir;

      val modules = files
        |> map (#1 #> Path.implode #> unsuffix ".hs" #> space_explode "/" #> space_implode ".");
      val _ =
        GHC.new_project tmp_dir
          {name = "isabelle",
           depends =
            ["bytestring", "containers", "network", "split", "threads", "utf8-string", "uuid"],
           modules = modules};

      val (out, rc) =
        Isabelle_System.bash_output
          (cat_lines ["set -e", "cd " ^ File.bash_path tmp_dir, "isabelle ghc_stack build 2>&1"]);
    in if rc = 0 then writeln out else error out end)
\<close>

end
