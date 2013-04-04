/*  Title:      Pure/Tools/main.scala
    Author:     Makarius

Default Isabelle application wrapper.
*/

package isabelle

import scala.swing.TextArea


object Main
{
  def main(args: Array[String])
  {
    val (out, rc) =
      try {
        GUI.init_laf()
        Isabelle_System.init()
        Isabelle_System.isabelle_tool("jedit", ("-s" :: args.toList): _*)
      }
      catch { case exn: Throwable => (Exn.message(exn), 2) }

    if (rc != 0)
      GUI.dialog(null, "Isabelle", "Isabelle output",
        GUI.scrollable_text(out + "\nReturn code: " + rc))

    sys.exit(rc)
  }
}

