/*  Title:      Pure/System/cygwin_init.scala
    Author:     Makarius

Initialize raw Isabelle distribution (e.g. after extraction via 7zip).
*/

package isabelle


import java.io.{File => JFile, BufferedReader, InputStreamReader}
import java.nio.file.Files

import scala.annotation.tailrec


object Cygwin_Init
{
  def filesystem(system_dialog: System_Dialog, isabelle_home: String)
  {
    system_dialog.title("Isabelle system initialization")
    system_dialog.echo("Initializing Cygwin:")

    def execute(args: String*): Int =
    {
      val cwd = new JFile(isabelle_home)
      val env = Map("CYGWIN" -> "nodosfilewarning")
      system_dialog.execute(cwd, env, args: _*)
    }

    val cygwin_root = isabelle_home + "\\contrib\\cygwin"

    system_dialog.echo("symlinks ...")
    val symlinks =
    {
      val path = (new JFile(cygwin_root + "\\isabelle\\symlinks")).toPath
      Files.readAllLines(path, UTF8.charset).toArray.toList.asInstanceOf[List[String]]
    }
    @tailrec def recover_symlinks(list: List[String]): Unit =
    {
      list match {
        case Nil | List("") =>
        case link :: content :: rest =>
          val path = (new JFile(isabelle_home, link)).toPath

          val writer = Files.newBufferedWriter(path, UTF8.charset)
          try { writer.write("!<symlink>" + content + "\0") }
          finally { writer.close }

          Files.setAttribute(path, "dos:system", true)

          recover_symlinks(rest)
        case _ => error("Unbalanced symlinks list")
      }
    }
    recover_symlinks(symlinks)

    system_dialog.echo("rebaseall ...")
    execute(cygwin_root + "\\bin\\dash.exe", "/isabelle/rebaseall")

    system_dialog.echo("postinstall ...")
    execute(cygwin_root + "\\bin\\bash.exe", "/isabelle/postinstall")

    system_dialog.echo("init ...")
    Isabelle_System.init()
    system_dialog.echo("OK")
  }
}

