(*  Title:      Tools/Haskell/Test.thy
    Author:     Makarius
*)

section \<open>Test build of Isabelle/Haskell modules\<close>

theory Test
  imports Haskell
begin

compile_generated_files _ (in Haskell)
  where \<open>fn dir =>
    let
      val modules =
        Generated_Files.get_files \<^theory>\<open>Haskell\<close>
        |> map (#path #> Path.implode #> unsuffix ".hs" #> space_explode "/" #> space_implode ".");
      val _ =
        GHC.new_project dir
          {name = "isabelle",
           depends =
            ["bytestring", "containers", "network", "split", "text", "threads", "uuid"],
           modules = modules};
    in
      writeln (Generated_Files.execute dir \<open>Build\<close> "mv Isabelle src && isabelle ghc_stack build")
    end\<close>

end
