/*  Title:      Pure/General/url.scala
    Author:     Makarius

Basic URL operations.
*/

package isabelle


import java.io.{File => JFile}
import java.nio.file.{Paths, FileSystemNotFoundException}
import java.net.{URI, URISyntaxException, URL, MalformedURLException, URLDecoder, URLEncoder}
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


  /* strings */

  def decode(s: String): String = URLDecoder.decode(s, UTF8.charset_name)
  def encode(s: String): String = URLEncoder.encode(s, UTF8.charset_name)


  /* read */

  private def read(url: URL, gzip: Boolean): String =
    using(url.openStream)(stream =>
      File.read_stream(if (gzip) new GZIPInputStream(stream) else stream))

  def read(url: URL): String = read(url, false)
  def read_gzip(url: URL): String = read(url, true)

  def read(name: String): String = read(Url(name), false)
  def read_gzip(name: String): String = read(Url(name), true)

  def read_bytes(url: URL): Bytes =
  {
    val connection = url.openConnection
    val length = connection.getContentLength
    using(connection.getInputStream)(Bytes.read_stream(_, hint = length))
  }


  /* file URIs */

  def print_file(file: JFile): String = File.absolute(file).toPath.toUri.toString
  def print_file_name(name: String): String = print_file(new JFile(name))

  def parse_file(uri: String): JFile = Paths.get(new URI(uri)).toFile

  def is_wellformed_file(uri: String): Boolean =
    try { parse_file(uri); true }
    catch {
      case _: URISyntaxException | _: IllegalArgumentException | _: FileSystemNotFoundException =>
        false
    }

  def absolute_file(uri: String): JFile = File.absolute(parse_file(uri))
  def absolute_file_name(uri: String): String = absolute_file(uri).getPath

  def canonical_file(uri: String): JFile = File.canonical(parse_file(uri))
  def canonical_file_name(uri: String): String = canonical_file(uri).getPath
}
