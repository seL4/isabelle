/*  Title:      Pure/General/mailman.scala
    Author:     Makarius

Support for Mailman list servers.
*/

package isabelle


import java.net.URL


object Mailman
{
  def archive(url: URL, name: String = ""): Archive =
  {
    val text = Url.read(url)
    val hrefs = """href="([^"]+\.txt(?:\.gz)?)"""".r.findAllMatchIn(text).map(_.group(1)).toList
    val title =
      """<title>The ([^</>]*) Archives</title>""".r.findFirstMatchIn(text).map(_.group(1))
    val list_name =
      (proper_string(name) orElse title).getOrElse(error("Failed to determine mailing list name"))
    new Archive(Url.trim_index(url), list_name, hrefs)
  }

  class Archive private[Mailman](val list_url: URL, val list_name: String, hrefs: List[String])
  {
    override def toString: String = list_name

    def download(
      target_dir: Path = Path.current,
      progress: Progress = new Progress): List[Path] =
    {
      val dir = target_dir + Path.basic(list_name)
      Isabelle_System.make_directory(dir)

      hrefs.flatMap(name =>
        {
          val path = dir + Path.basic(name)
          val url = new URL(list_url, name)
          val connection = url.openConnection
          try {
            val length = connection.getContentLengthLong
            val timestamp = connection.getLastModified
            val file = path.file
            if (file.isFile && file.length == length && file.lastModified == timestamp) None
            else {
              progress.echo("Getting " + url)
              val bytes =
                using(connection.getInputStream)(Bytes.read_stream(_, hint = length.toInt max 1024))
              Bytes.write(file, bytes)
              file.setLastModified(timestamp)
              Some(path)
            }
          }
          finally { connection.getInputStream.close }
        })
    }
  }
}
