/*  Title:      Pure/General/url.scala
    Author:     Makarius

Basic URL operations.
*/

package isabelle


import java.io.{File => JFile}
import java.net.{URI, URISyntaxException}
import java.net.{URL, MalformedURLException}
import java.util.zip.GZIPInputStream


object Url
{
  def escape(name: String): String =
    (for (c <- name.iterator) yield if (c == '\'') "%27" else new String(Array(c))).mkString

  def apply(name: String): URL =
  {
    try { new URL(name) }
    catch { case _: MalformedURLException => error("Malformed URL " + quote(name)) }
  }

  def is_wellformed(name: String): Boolean =
    try { Url(name); true }
    catch { case ERROR(_) => false }

  def is_readable(name: String): Boolean =
    try { Url(name).openStream.close; true }
    catch { case ERROR(_) => false }


  /* read */

  private def read(url: URL, gzip: Boolean): String =
  {
    val stream = url.openStream
    try { File.read_stream(if (gzip) new GZIPInputStream(stream) else stream) }
    finally { stream.close }
  }

  def read(url: URL): String = read(url, false)
  def read_gzip(url: URL): String = read(url, true)

  def read(name: String): String = read(Url(name), false)
  def read_gzip(name: String): String = read(Url(name), true)


  /* file URIs */

  def file(uri: String): JFile = new JFile(new URI(uri))

  def is_wellformed_file(uri: String): Boolean =
    try { file(uri); true }
    catch { case _: URISyntaxException | _: IllegalArgumentException => false }

  def normalize_file(uri: String): String =
    if (is_wellformed_file(uri)) {
      val uri1 = new URI(uri).normalize.toASCIIString
      if (uri1.startsWith("file://")) uri1
      else {
        Library.try_unprefix("file:/", uri1) match {
          case Some(p) => "file:///" + p
          case None => uri1
        }
      }
    }
    else uri

  def platform_file(path: Path): String =
  {
    val path1 = path.expand
    require(path1.is_absolute)
    platform_file(File.platform_path(path1))
  }

  def platform_file(name: String): String =
    if (name.startsWith("file://")) name
    else {
      val s = name.replaceAll(" ", "%20")
      if (!Platform.is_windows) "file://" + s
      else if (s.startsWith("\\\\")) "file:" + s.replace('\\', '/')
      else "file:///" + s.replace('\\', '/')
    }
}
