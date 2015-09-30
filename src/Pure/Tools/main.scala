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
    val start =
    {
      try {
        Isabelle_System.init()


        /* settings directory */

        val settings_dir = Path.explode("$JEDIT_SETTINGS")
        Isabelle_System.mkdirs(settings_dir + Path.explode("DockableWindowManager"))

        if (!(settings_dir + Path.explode("perspective.xml")).is_file) {
          File.write(settings_dir + Path.explode("DockableWindowManager/perspective-view0.xml"),
            """<DOCKING LEFT="" TOP="" RIGHT="isabelle-documentation" BOTTOM="" LEFT_POS="0" TOP_POS="0" RIGHT_POS="250" BOTTOM_POS="250" />""")
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
          Array("-settings=" + File.platform_path(Path.explode("$JEDIT_SETTINGS")))

        val more_args =
          if (args.isEmpty)
            Array(File.platform_path(Path.explode("$USER_HOME/Scratch.thy")))
          else args


        /* main startup */

        update_environment()

        System.setProperty("jedit.home", File.platform_path(Path.explode("$JEDIT_HOME/dist")))
        System.setProperty("scala.home", File.platform_path(Path.explode("$SCALA_HOME")))

        val jedit =
          Class.forName("org.gjt.sp.jedit.jEdit", true, ClassLoader.getSystemClassLoader)
        val jedit_main = jedit.getMethod("main", classOf[Array[String]])

        () => jedit_main.invoke(null, jedit_options ++ jedit_settings ++ more_args)
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


  /* adhoc update of JVM environment variables */

  def update_environment()
  {
    val update =
    {
      val isabelle_home = Isabelle_System.getenv("ISABELLE_HOME")
      val isabelle_home_user = Isabelle_System.getenv("ISABELLE_HOME_USER")

      (env0: Any) => {
        val env = env0.asInstanceOf[java.util.Map[String, String]]
        env.put("ISABELLE_HOME", File.platform_path(isabelle_home))
        env.put("ISABELLE_HOME_USER", File.platform_path(isabelle_home_user))
      }
    }

    classOf[java.util.Collections].getDeclaredClasses
      .find(c => c.getName == "java.util.Collections$UnmodifiableMap") match
    {
      case Some(c) =>
        val m = c.getDeclaredField("m")
        m.setAccessible(true)
        update(m.get(System.getenv()))

        if (Platform.is_windows) {
          val ProcessEnvironment = Class.forName("java.lang.ProcessEnvironment")
          val field = ProcessEnvironment.getDeclaredField("theCaseInsensitiveEnvironment")
          field.setAccessible(true)
          update(field.get(null))
        }

      case None =>
        error("Failed to update JVM environment -- platform incompatibility")
    }
  }
}
