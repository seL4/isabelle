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
    Platform.init_laf()
    Isabelle_System.init()

    System.setProperty("jedit.home",
      Isabelle_System.platform_path(Path.explode("$JEDIT_HOME/dist")))

    // FIXME properties from JEDIT_JAVA_OPTIONS JEDIT_SYSTEM_OPTIONS
    val jedit_options = Isabelle_System.getenv_strict("JEDIT_OPTIONS").split(" +")
    val jedit_settings =
      Array("-settings=" + Isabelle_System.platform_path(Path.explode("$JEDIT_SETTINGS")))
    jEdit.main(jedit_options ++ jedit_settings ++ args)
  }
}

