/*  Title:      Pure/General/url.scala
    Author:     Makarius

Basic URL operations.
*/

package isabelle


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

  private def gen_read(name: String, gzip: Boolean): String =
  {
    val stream = Url(name).openStream
    try { File.read_stream(if (gzip) new GZIPInputStream(stream) else stream) }
    finally { stream.close }
  }

  def read(name: String): String = gen_read(name, false)
  def read_gzip(name: String): String = gen_read(name, true)
}
