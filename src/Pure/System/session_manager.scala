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
  private def find_sessions(rev_prefix: List[String], rev_sessions: List[List[String]],
    dir: File): List[List[String]] =
  {
    val (rev_prefix1, rev_sessions1) =
      if (is_session_dir(dir)) {
        val name = dir.getName  // FIXME from root file
        val rev_prefix1 = name :: rev_prefix
        val rev_sessions1 = rev_prefix1.reverse :: rev_sessions
        (rev_prefix1, rev_sessions1)
      }
      else (rev_prefix, rev_sessions)

    val subdirs =
      dir.listFiles(new FileFilter { def accept(entry: File) = entry.isDirectory })
    (rev_sessions1 /: subdirs)(find_sessions(rev_prefix1, _, _))
  }

  def component_sessions(): List[List[String]] =
  {
    val toplevel_sessions =
      system.components().map(system.platform_file(_)).filter(is_session_dir)
    ((Nil: List[List[String]]) /: toplevel_sessions)(find_sessions(Nil, _, _)).reverse
  }
}
