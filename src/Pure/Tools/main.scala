/*  Title:      Pure/Tools/main.scala
    Author:     Makarius

Main Isabelle application entry point.
*/

package isabelle


import java.lang.System
import java.io.{File => JFile}


object Main
{
  def main(args: Array[String])
  {
    def start: Unit =
    {
      val (out, rc) =
        try {
          GUI.init_laf()
          Isabelle_System.init()
          Isabelle_System.isabelle_tool("jedit", ("-s" :: "--" :: args.toList): _*)
        }
        catch { case exn: Throwable => (Exn.message(exn), 2) }

      if (rc != 0)
        GUI.dialog(null, "Isabelle", "Isabelle output",
          GUI.scrollable_text(out + "\nReturn code: " + rc))

      sys.exit(rc)
    }

    if (Platform.is_windows) {
      val init_isabelle_home =
        try {
          GUI.init_laf()

          val isabelle_home0 = System.getenv("ISABELLE_HOME_WINDOWS")
          val isabelle_home = System.getProperty("isabelle.home")

          if (isabelle_home0 != null && isabelle_home0 != "") None
          else {
            if (isabelle_home == null || isabelle_home == "")
              error("Unknown Isabelle home directory")
            if (!(new JFile(isabelle_home)).isDirectory)
              error("Bad Isabelle home directory: " + quote(isabelle_home))

            val uninitialized_file =
              new JFile(isabelle_home, "contrib\\cygwin\\isabelle\\uninitialized")
            val uninitialized = uninitialized_file.isFile && uninitialized_file.delete

            if (uninitialized) Some(isabelle_home) else None
          }
        }
        catch {
          case exn: Throwable =>
            GUI.dialog(null, "Isabelle", GUI.scrollable_text(Exn.message(exn)))
            sys.exit(2)
        }
      init_isabelle_home match {
        case Some(isabelle_home) =>
          GUI.dialog(null, "Isabelle", GUI.scrollable_text("OK"))
          Swing_Thread.later { Cygwin_Init.main_frame(isabelle_home, start) }
        case None => start
      }
    }
    else start
  }
}

