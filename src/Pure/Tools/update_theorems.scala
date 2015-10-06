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
      args.foreach(arg => update_theorems(Path.explode(arg)))
    }
  }
}
