/*  Title:      Pure/System/cygwin.scala
    Module:     PIDE
    Author:     Makarius

Accessing the Cygwin installation.
*/

package isabelle

import java.lang.System
import java.io.File
import java.net.URL
import java.awt.Component


object Cygwin
{
  /* Cygwin installation */

  private def sanity_check(root: File)
  {
    if (!new File(root, "bin\\bash.exe").isFile ||
        !new File(root, "bin\\env.exe").isFile ||
        !new File(root, "bin\\tar.exe").isFile)
      error("Bad Cygwin installation: " + root.toString)
  }

  def check_root(): String =
  {
    val cygwin_root1 = System.getenv("CYGWIN_ROOT")
    val cygwin_root2 = System.getProperty("cygwin.root")
    val root =
      if (cygwin_root1 != null && cygwin_root1 != "") cygwin_root1
      else if (cygwin_root2 != null && cygwin_root2 != "") cygwin_root2
      else error("Bad Cygwin installation: unknown root")
    sanity_check(new File(root))
    root
  }
}

