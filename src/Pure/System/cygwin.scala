/*  Title:      Pure/System/cygwin.scala
    Author:     Makarius

Support for Cygwin.
*/

package isabelle


import java.io.{File => JFile}
import java.nio.file.{Paths, Files}


object Cygwin
{
  /* symlinks */

  def write_symlink(file: JFile, content: String)
  {
    require(Platform.is_windows)

    val path = file.toPath

    val writer = Files.newBufferedWriter(path, UTF8.charset)
    try { writer.write("!<symlink>" + content + "\0") }
    finally { writer.close }

    Files.setAttribute(path, "dos:system", true)
  }
}

