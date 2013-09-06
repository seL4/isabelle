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

    val file_args =
      if (args.isEmpty)
        Array(Isabelle_System.platform_path(Path.explode("$USER_HOME/Scratch.thy")))
      else args

    val jedit_options =
      Isabelle_System.getenv_strict("JEDIT_OPTIONS").split(" +")

    val jedit_settings =
      Array("-settings=" + Isabelle_System.platform_path(Path.explode("$JEDIT_SETTINGS")))

    System.setProperty("jedit.home",
      Isabelle_System.platform_path(Path.explode("$JEDIT_HOME/dist")))

    jEdit.main(jedit_options ++ jedit_settings ++ file_args)
  }
}

