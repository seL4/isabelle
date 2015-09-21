/*  Title:      Pure/Tools/update_then.scala
    Author:     Makarius

Expand old Isar command conflations 'hence' and 'thus'.
*/

package isabelle


object Update_Then
{
  def update_then(path: Path)
  {
    val text0 = File.read(path)
    val text1 =
      (for (tok <- Token.explode(Keyword.Keywords.empty, text0).iterator)
        yield {
          tok.source match {
            case "hence" => "then have"
            case "thus" => "then show"
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
      args.foreach(arg => update_then(Path.explode(arg)))
    }
  }
}
