/*  Title:      Pure/Tools/update_theorems.scala
    Author:     Makarius

Update toplevel theorem keywords.
*/

package isabelle


object Update_Theorems
{
  def update_theorems(path: Path)
  {
    val text0 = File.read(path)
    val text1 =
      (for (tok <- Token.explode(Keyword.Keywords.empty, text0).iterator)
        yield {
          tok.source match {
            case "theorems" => "lemmas"
            case "schematic_theorem" | "schematic_lemma" | "schematic_corollary" =>
              "schematic_goal"
            case s => s
        } }).mkString

    if (text0 != text1) {
      Output.writeln("changing " + path)
      File.write_backup2(path, text1)
    }
  }


  /* command line entry point */

  def main(args: Array[String])
  {
    Command_Line.tool0 {
      val getopts = Getopts("""
Usage: isabelle update_theorems [FILES|DIRS...]

  Recursively find .thy files and update toplevel theorem keywords:

    theorems             ~>  lemmas
    schematic_theorem    ~>  schematic_goal
    schematic_lemma      ~>  schematic_goal
    schematic_corollary  ~>  schematic_goal

  Old versions of files are preserved by appending "~~".
""")

      val specs = getopts(args)
      if (specs.isEmpty) getopts.usage()

      for {
        spec <- specs
        file <- File.find_files(Path.explode(spec).file, file => file.getName.endsWith(".thy"))
      } update_theorems(Path.explode(File.standard_path(file)))
    }
  }
}
