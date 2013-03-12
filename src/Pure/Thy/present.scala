/*  Title:      Pure/Thy/present.scala
    Author:     Makarius

Theory presentation: HTML.
*/

package isabelle


object Present
{
  /* maintain chapter index -- NOT thread-safe */

  private val index_path = Path.basic("index.html")
  private val sessions_path = Path.basic(".sessions")

  private def read_sessions(dir: Path): List[String] =
    split_lines(File.read(dir + sessions_path))

  private def write_sessions(dir: Path, sessions: List[String]): Unit =
    File.write(dir + sessions_path, cat_lines(sessions))

  def update_chapter_index(info_path: Path, chapter: String, new_sessions: List[String]): Unit =
  {
    val dir = info_path + Path.basic(chapter)
    Isabelle_System.mkdirs(dir)

    val sessions0 =
      try { split_lines(File.read(dir + sessions_path)) }
      catch { case ERROR(_) => Nil }

    val sessions = sessions0.filterNot(new_sessions.contains) ::: new_sessions
    write_sessions(dir, sessions)
    File.write(dir + index_path, HTML.chapter_index(chapter, sessions))
  }
}

