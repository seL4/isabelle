/*  Title:      Pure/System/isabelle_manager.scala
    Author:     Makarius

Isabelle session manager.
*/

package isabelle


import java.io.{File, FileFilter}


class Session_Manager(system: Isabelle_System)
{
  val ROOT_NAME = "session.root"

  def is_session_file(file: File): Boolean =
    file.isFile && file.getName == ROOT_NAME

  def is_session_dir(dir: File): Boolean =
    dir.isDirectory && (new File(dir, ROOT_NAME)).isFile


  // FIXME handle (potentially cyclic) directory graph
  private def find_sessions(reverse_prefix: List[String], reverse_sessions: List[List[String]],
    dir: File): List[List[String]] =
  {
    val (reverse_prefix1, reverse_sessions1) =
      if (is_session_dir(dir)) {
        val name = dir.getName  // FIXME from root file
        val reverse_prefix1 = name :: reverse_prefix
        val reverse_sessions1 = reverse_prefix1.reverse :: reverse_sessions
        (reverse_prefix1, reverse_sessions1)
      }
      else (reverse_prefix, reverse_sessions)

    val subdirs =
      dir.listFiles(new FileFilter { def accept(entry: File) = entry.isDirectory })
    (reverse_sessions1 /: subdirs)(find_sessions(reverse_prefix1, _, _))
  }

  def component_sessions(): List[List[String]] =
  {
    val toplevel_sessions =
      system.components().map(system.platform_file(_)).filter(is_session_dir)
    ((Nil: List[List[String]]) /: toplevel_sessions)(find_sessions(Nil, _, _)).reverse
  }
}
