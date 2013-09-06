/*  Title:      Tools/jEdit/src/jedit_main.scala
    Author:     Makarius

Main entry point from running JVM.
*/

package isabelle.jedit


import isabelle._


import org.gjt.sp.jedit.jEdit


object JEdit_Main
{
  def main(args: Array[String])
  {
    GUI.init_laf()
    Isabelle_System.init()


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

    jEdit.main(jedit_options ++ jedit_settings ++ more_args)
  }
}

