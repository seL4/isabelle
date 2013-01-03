/*  Title:      Pure/Thy/present.scala
    Author:     Makarius

Theory presentation: HTML.
*/

package isabelle


object Present
{
  /* maintain session index -- NOT thread-safe */

  private val index_path = Path.basic("index.html")
  private val session_entries_path = Path.explode(".session/entries")
  private val pre_index_path = Path.explode(".session/pre-index")

  private def get_entries(dir: Path): List[String] =
    split_lines(File.read(dir + session_entries_path))

  private def put_entries(entries: List[String], dir: Path): Unit =
    File.write(dir + session_entries_path, cat_lines(entries))

  def create_index(dir: Path): Unit =
    File.write(dir + index_path,
      File.read(dir + pre_index_path) +
      HTML.session_entries(get_entries(dir)) +
      HTML.end_document)

  def update_index(dir: Path, names: List[String]): Unit =
    try {
      put_entries(get_entries(dir).filterNot(names.contains) ::: names, dir)
      create_index(dir)
    }
    catch {
      case ERROR(msg) =>
        java.lang.System.err.println(
          "### " + msg + "\n### Browser info: failed to update session index of " + dir)
    }
}

