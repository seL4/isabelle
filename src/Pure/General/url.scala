/*  Title:      Pure/General/url.scala
    Author:     Makarius

Basic URL operations.
*/

package isabelle


import java.io.{File => JFile}
import java.nio.file.Paths
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

  def print_file(file: JFile): String =
    file.toPath.toAbsolutePath.toUri.normalize.toString

  def parse_file(uri: String): JFile = Paths.get(new URI(uri)).toFile

  def is_wellformed_file(uri: String): Boolean =
    try { parse_file(uri); true }
    catch { case _: URISyntaxException | _: IllegalArgumentException => false }

  def normalize_file(uri: String): String =
    if (is_wellformed_file(uri)) print_file(parse_file(uri)) else uri
}
