/*  Title:      Pure/Tools/main.scala
    Author:     Makarius

Main Isabelle application entry point.
*/

package isabelle


import javax.swing.SwingUtilities
import java.lang.{System, ClassLoader}
import java.io.{File => JFile}


object Main
{
  private def continue(body: => Unit)(rc: Int)
  {
    if (rc != 0) sys.exit(rc)
    else if (SwingUtilities.isEventDispatchThread())
      Simple_Thread.fork("Isabelle") { body }
    else body
  }

  def main(args: Array[String])
  {
    val system_dialog = new System_Dialog

    def exit_error(exn: Throwable): Nothing =
    {
      GUI.dialog(null, "Isabelle", GUI.scrollable_text(Exn.message(exn)))
      system_dialog.return_code(2)
      sys.exit(system_dialog.join)
    }

    def run
    {
      build
      val rc = system_dialog.join
      if (rc == 0) start
      else sys.exit(rc)
    }

    def build
    {
      try {
        GUI.init_laf()
        Isabelle_System.init()

        val mode = Isabelle_System.getenv("JEDIT_BUILD_MODE")
        if (mode == "none")
          system_dialog.return_code(0)
        else {
          val system_mode = mode == "" || mode == "system"
          val dirs = Path.split(Isabelle_System.getenv("JEDIT_SESSION_DIRS"))
          val options = Options.init()
          val session = Isabelle_System.default_logic(
            Isabelle_System.getenv("JEDIT_LOGIC"),
            options.string("jedit_logic"))
          Build_Dialog.dialog(options, system_dialog, system_mode, dirs, session)
        }
      }
      catch { case exn: Throwable => exit_error(exn) }
    }

    def start
    {
      val do_start =
      {
        try {
          /* settings directory */

          val settings_dir = Path.explode("$JEDIT_SETTINGS")
          Isabelle_System.mkdirs(settings_dir + Path.explode("DockableWindowManager"))

          if (!(settings_dir + Path.explode("perspective.xml")).is_file) {
            File.write(settings_dir + Path.explode("DockableWindowManager/perspective-view0.xml"),
              """<DOCKING LEFT="" TOP="" RIGHT="" BOTTOM="isabelle-readme" LEFT_POS="0" TOP_POS="0" RIGHT_POS="250" BOTTOM_POS="250" />""")
            File.write(settings_dir + Path.explode("perspective.xml"),
              """<?xml version="1.0" encoding="UTF-8" ?>
<!DOCTYPE PERSPECTIVE SYSTEM "perspective.dtd">
<PERSPECTIVE>
<VIEW PLAIN="FALSE">
<GEOMETRY X="0" Y="35" WIDTH="1072" HEIGHT="787" EXT_STATE="0" />
</VIEW>
</PERSPECTIVE>""")
          }


          /* args */

          val jedit_options =
            Isabelle_System.getenv_strict("JEDIT_OPTIONS").split(" +")

          val jedit_settings =
            Array("-settings=" + Isabelle_System.platform_path(Path.explode("$JEDIT_SETTINGS")))

          val more_args =
            if (args.isEmpty)
              Array(Isabelle_System.platform_path(Path.explode("$USER_HOME/Scratch.thy")))
            else args


          /* startup */

          System.setProperty("jedit.home",
            Isabelle_System.platform_path(Path.explode("$JEDIT_HOME/dist")))

          System.setProperty("scala.home",
            Isabelle_System.platform_path(Path.explode("$SCALA_HOME")))

          val jedit = ClassLoader.getSystemClassLoader.loadClass("org.gjt.sp.jedit.jEdit")
          val jedit_main = jedit.getDeclaredMethod("main", classOf[Array[String]])

          () => jedit_main.invoke(null, jedit_options ++ jedit_settings ++ more_args)
        }
        catch { case exn: Throwable => exit_error(exn) }
      }
      do_start()
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

            val cygwin_root = isabelle_home + "\\contrib\\cygwin"
            if ((new JFile(cygwin_root)).isDirectory)
              System.setProperty("cygwin.root", cygwin_root)

            val uninitialized_file = new JFile(cygwin_root, "isabelle\\uninitialized")
            val uninitialized = uninitialized_file.isFile && uninitialized_file.delete

            if (uninitialized) Some(isabelle_home) else None
          }
        }
        catch { case exn: Throwable => exit_error(exn) }

      init_isabelle_home match {
        case Some(isabelle_home) =>
          Swing_Thread.later { Cygwin_Init.main_frame(isabelle_home, continue(run)) }
        case None => run
      }
    }
    else run
  }
}

