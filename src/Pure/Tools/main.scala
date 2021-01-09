/*  Title:      Pure/Tools/main.scala
    Author:     Makarius

Main Isabelle application entry point.
*/

package isabelle


import java.lang.{Class, ClassLoader}


object Main
{
  /* main entry point */

  def main(args: Array[String])
  {
    if (args.nonEmpty && args(0) == "-init") {
      Isabelle_System.init()
    }
    else {
      val start =
      {
        try {
          Isabelle_System.init()
          Isabelle_Fonts.init()

          GUI.init_lafs()


          /* ROOTS template */

          {
            val roots = Path.explode("$ISABELLE_HOME_USER/ROOTS")
            if (!roots.is_file) File.write(roots, """# Additional session root directories
#
#   * each line contains one directory entry in Isabelle path notation
#   * lines starting with "#" are stripped
#   * changes require application restart
#
#:mode=text:encoding=UTF-8:
""")
          }


          /* settings directory */

          val settings_dir = Path.explode("$JEDIT_SETTINGS")

          val properties = settings_dir + Path.explode("properties")
          if (properties.is_file) {
            val props1 = split_lines(File.read(properties))
            val props2 = props1.filterNot(_.startsWith("plugin-blacklist.Isabelle-jEdit"))
            if (props1 != props2) File.write(properties, cat_lines(props2))
          }

          Isabelle_System.make_directory(settings_dir + Path.explode("DockableWindowManager"))

          if (!(settings_dir + Path.explode("perspective.xml")).is_file) {
            File.write(settings_dir + Path.explode("DockableWindowManager/perspective-view0.xml"),
              """<DOCKING LEFT="isabelle-documentation" TOP="" RIGHT="isabelle-theories" BOTTOM="" LEFT_POS="250" TOP_POS="0" RIGHT_POS="250" BOTTOM_POS="250" />""")
            File.write(settings_dir + Path.explode("perspective.xml"),
              XML.header +
"""<!DOCTYPE PERSPECTIVE SYSTEM "perspective.dtd">
<PERSPECTIVE>
<VIEW PLAIN="FALSE">
<GEOMETRY X="0" Y="35" WIDTH="1200" HEIGHT="850" EXT_STATE="0" />
</VIEW>
</PERSPECTIVE>""")
          }


          /* args */

          val jedit_settings =
            "-settings=" + File.platform_path(Path.explode("$JEDIT_SETTINGS"))

          val jedit_server =
            System.getProperty("isabelle.jedit_server") match {
              case null | "" => "-noserver"
              case name => "-server=" + name
            }

          val jedit_options =
            Isabelle_System.getenv_strict("JEDIT_OPTIONS").split(" +")

          val more_args =
          {
            args.toList.dropWhile(arg => arg.startsWith("-") && arg != "--") match {
              case Nil | List("--") =>
                args ++ Array(File.platform_path(Path.explode("$USER_HOME/Scratch.thy")))
              case List(":") => args.slice(0, args.size - 1)
              case _ => args
            }
          }


          /* environment */

          def putenv(name: String, value: String)
          {
            val misc =
              Class.forName("org.gjt.sp.jedit.MiscUtilities", true, ClassLoader.getSystemClassLoader)
            val putenv = misc.getMethod("putenv", classOf[String], classOf[String])
            putenv.invoke(null, name, value)
          }

          for (name <- List("ISABELLE_HOME", "ISABELLE_HOME_USER", "JEDIT_HOME", "JEDIT_SETTINGS")) {
            putenv(name, File.platform_path(Isabelle_System.getenv(name)))
          }
          putenv("ISABELLE_ROOT", null)


          /* properties */

          System.setProperty("jedit.home", File.platform_path(Path.explode("$JEDIT_HOME/dist")))
          System.setProperty("scala.home", File.platform_path(Path.explode("$SCALA_HOME")))
          System.setProperty("scala.color", "false")


          /* main startup */

          val jedit =
            Class.forName("org.gjt.sp.jedit.jEdit", true, ClassLoader.getSystemClassLoader)
          val jedit_main = jedit.getMethod("main", classOf[Array[String]])

          () => jedit_main.invoke(
            null, Array(jedit_settings, jedit_server) ++ jedit_options ++ more_args)
        }
        catch {
          case exn: Throwable =>
            GUI.init_laf()
            GUI.dialog(null, "Isabelle", GUI.scrollable_text(Exn.message(exn)))
            sys.exit(2)
        }
      }
      start()
    }
  }
}
