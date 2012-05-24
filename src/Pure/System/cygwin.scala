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

  def setup(parent: Component, root: File)
  {
    if (!root.isDirectory && !root.mkdirs) error("Failed to create root directory: " + root)

    val download = new File(root, "download")
    if (!download.mkdir) error("Failed to create download directory: " + download)

    val setup_exe = new File(root, "setup.exe")

    try {
      Download.file(parent, "Downloading", new URL("http://www.cygwin.com/setup.exe"), setup_exe)
    }
    catch { case ERROR(_) => error("Failed to download Cygwin setup program") }

    val (_, rc) = Standard_System.raw_exec(root, null, true,
        setup_exe.toString, "-R", root.toString, "-l", download.toString,
          "-P", "libgmp3,make,perl,python", "-q", "-n")
    if (rc != 0) error("Cygwin setup failed!")

    sanity_check(root)
  }
}

