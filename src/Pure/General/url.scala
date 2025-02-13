/*  Title:      Pure/General/url.scala
    Author:     Makarius

Basic URL/URI operations.
*/

package isabelle


import java.io.{File => JFile, InputStream}
import java.nio.file.{Paths, FileSystemNotFoundException}
import java.net.{URI, URISyntaxException, MalformedURLException, URLDecoder, URLEncoder,
  URLConnection}
import java.util.Locale
import java.util.zip.GZIPInputStream


object Url {
  /* special characters */

  def escape_special(c: Char): String =
    if ("!#$&'()*+,/:;=?@[]".contains(c)) {
      String.format(Locale.ROOT, "%%%02X", Integer.valueOf(c.toInt))
    }
    else c.toString

  def escape_special(s: String): String = s.iterator.map(escape_special).mkString

  def escape_name(name: String): String =
    name.iterator.map({ case '\'' => "%27" case c => c.toString }).mkString


  /* make and check URLs */

  def is_malformed(exn: Throwable): Boolean =
    exn.isInstanceOf[MalformedURLException] ||
    exn.isInstanceOf[URISyntaxException] ||
    exn.isInstanceOf[IllegalArgumentException]

  def apply(uri: URI): Url = new Url(uri)

  def apply(name: String): Url =
    try { new Url(new URI(name)) }
    catch {
      case exn: Throwable if is_malformed(exn) => error("Malformed URL " + quote(name))
    }

  def is_wellformed(name: String): Boolean =
    try { Url(name); true }
    catch { case ERROR(_) => false }

  def is_readable(name: String): Boolean =
    try { Url(name).open_stream().close(); true }
    catch { case ERROR(_) => false }


  /* file name */

  def file_name(url: Url): String =
    Library.take_suffix[Char](c => c != '/' && c != '\\', url.java_url.getFile.toList)._2.mkString

  def trim_index(url: Url): Url = {
    Library.try_unprefix("/index.html", url.toString) match {
      case Some(u) => Url(u)
      case None =>
        Library.try_unprefix("/index.php", url.toString) match {
          case Some(u) => Url(u)
          case None => url
        }
    }
  }


  /* strings */

  def decode(s: String): String = URLDecoder.decode(s, UTF8.charset)
  def encode(s: String): String = URLEncoder.encode(s, UTF8.charset)


  /* read */

  private def read(url: Url, gzip: Boolean): String =
    using(url.open_stream())(stream =>
      File.read_stream(if (gzip) new GZIPInputStream(stream) else stream))

  def read(url: Url): String = read(url, false)
  def read_gzip(url: Url): String = read(url, true)

  def read(name: String): String = read(Url(name), false)
  def read_gzip(name: String): String = read(Url(name), true)


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


  /* generic path notation: standard, platform, ssh, rsync, ftp, http, https */

  private val separators1 = "/\\"
  private val separators2 = ":/\\"

  def is_base_name(s: String, suffix: String = ""): Boolean =
    s.nonEmpty && !s.exists(separators2.contains) && s.endsWith(suffix)

  def get_base_name(s: String, suffix: String = ""): Option[String] = {
    val i = s.lastIndexWhere(separators2.contains)
    if (i + 1 >= s.length) None else Library.try_unsuffix(suffix, s.substring(i + 1))
  }

  def strip_base_name(s: String, suffix: String = ""): Option[String] = {
    val i = s.lastIndexWhere(separators2.contains)
    val j = s.lastIndexWhere(c => !separators1.contains(c), end = i)
    if (i + 1 >= s.length || !s.endsWith(suffix)) None
    else if (j < 0) Some(s.substring(0, i + 1))
    else Some(s.substring(0, j + 1))
  }

  def get_ext(str: String): String = {
    val s = get_base_name(str).getOrElse("")
    val i = s.lastIndexOf('.')
    if (i < 0 || i + 1 >= s.length) "" else s.substring(i + 1)
  }

  def append_path(prefix: String, suffix: String): String =
    if (prefix.endsWith(":") || prefix.endsWith("/") || prefix.endsWith("\\") || prefix.isEmpty) {
      prefix + suffix
    }
    else if (prefix.endsWith(":.") || prefix.endsWith("/.") || prefix.endsWith("\\.") || prefix == ".") {
      prefix.substring(0, prefix.length - 1) + suffix
    }
    else if (prefix.contains('\\') || suffix.contains('\\')) {
      prefix + "\\" + suffix
    }
    else prefix + "/" + suffix

  def direct_path(prefix: String): String = append_path(prefix, ".")

  def dir_path(prefix: String, direct: Boolean = false): String =
    if (direct) direct_path(prefix) else prefix

  def index_path(prefix: String = "", index: String = ""): String =
    append_path(prefix, if (index.isEmpty) "index.html" else index)
}

final class Url private(val uri: URI) {
  override def toString: String = uri.toString

  override def hashCode: Int = uri.hashCode
  override def equals(obj: Any): Boolean =
    obj match {
      case other: Url => uri == other.uri
      case _ => false
    }

  def resolve(route: String): Url =
    if (route.isEmpty) this else new Url(uri.resolve(route))

  val java_url: java.net.URL = uri.toURL
  def open_stream(): InputStream = java_url.openStream()
  def open_connection(): URLConnection = java_url.openConnection()
}
