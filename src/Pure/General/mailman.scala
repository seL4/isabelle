/*  Title:      Pure/General/mailman.scala
    Author:     Makarius

Support for Mailman list servers.
*/

package isabelle


import java.net.URL

import scala.util.matching.Regex


object Mailman
{
  /* mailing list archives */

  def archive(url: URL, msg_format: Msg_Format, name: String = ""): Archive =
  {
    val list_url =
      Url(Library.take_suffix[Char](_ == '/', Url.trim_index(url).toString.toList)._1.mkString + "/")

    val html = Url.read(list_url)
    val title =
      """<title>The ([^</>]*) Archives</title>""".r.findFirstMatchIn(html).map(_.group(1))
    val hrefs_text =
      """href="([^"]+\.txt(?:\.gz)?)"""".r.findAllMatchIn(html).map(_.group(1)).toList

    val list_name =
      (proper_string(name) orElse title).getOrElse(error("Failed to determine mailing list name"))
    new Archive(list_url, list_name, msg_format, hrefs_text)
  }

  abstract class Msg_Format
  {
    def regex: Regex
  }

  class Archive private[Mailman](
    val list_url: URL,
    val list_name: String,
    msg_format: Msg_Format,
    hrefs_text: List[String])
  {
    override def toString: String = list_name

    private def hrefs_msg: List[String] =
      (for {
        href <- """href="([^"]+)/date.html"""".r.findAllMatchIn(Url.read(list_url)).map(_.group(1))
        html = Url.read(new URL(list_url, href + "/date.html"))
        msg <- msg_format.regex.findAllMatchIn(html).map(_.group(1))
      } yield href + "/" + msg).toList

    def get(target_dir: Path, href: String, progress: Progress = new Progress): Option[Path] =
    {
      val dir = target_dir + Path.basic(list_name)
      val path = dir + Path.explode(href)
      val url = new URL(list_url, href)
      val connection = url.openConnection
      try {
        val length = connection.getContentLengthLong
        val timestamp = connection.getLastModified
        val file = path.file
        if (file.isFile && file.length == length && file.lastModified == timestamp) None
        else {
          Isabelle_System.make_directory(path.dir)
          progress.echo("Getting " + url)
          val bytes =
            using(connection.getInputStream)(Bytes.read_stream(_, hint = length.toInt max 1024))
          Bytes.write(file, bytes)
          file.setLastModified(timestamp)
          Some(path)
        }
      }
      finally { connection.getInputStream.close() }
    }

    def download_text(target_dir: Path, progress: Progress = new Progress): List[Path] =
      hrefs_text.flatMap(get(target_dir, _, progress = progress))

    def download_msg(target_dir: Path, progress: Progress = new Progress): List[Path] =
      hrefs_msg.flatMap(get(target_dir, _, progress = progress))

    def download(target_dir: Path, progress: Progress = new Progress): List[Path] =
      download_text(target_dir, progress = progress) :::
      download_msg(target_dir, progress = progress)
  }


  /* Isabelle mailing lists */

  def isabelle_users: Archive =
    archive(Url("https://lists.cam.ac.uk/pipermail/cl-isabelle-users"), name = "isabelle-users",
      msg_format =
        new Msg_Format { val regex: Regex = """<li><a name="\d+" href="(msg\d+\.html)">""".r })

  def isabelle_dev: Archive =
    archive(Url("https://mailmanbroy.in.tum.de/pipermail/isabelle-dev"),
      new Msg_Format { val regex: Regex = """<LI><A HREF="(\d+\.html)">""".r })
}
