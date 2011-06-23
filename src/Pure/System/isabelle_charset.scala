/*  Title:      Pure/System/isabelle_charset.scala
    Author:     Makarius

Charset for Isabelle symbols.
*/

package isabelle

import java.nio.Buffer
import java.nio.{ByteBuffer, CharBuffer}
import java.nio.charset.{Charset, CharsetDecoder, CharsetEncoder, CoderResult}
import java.nio.charset.spi.CharsetProvider


object Isabelle_Charset
{
  val name: String = "UTF-8-Isabelle-test"  // FIXME
  lazy val charset: Charset = new Isabelle_Charset
}


class Isabelle_Charset extends Charset(Isabelle_Charset.name, null)
{
  override def contains(cs: Charset): Boolean =
    cs.name.equalsIgnoreCase(Standard_System.charset_name) ||
    Standard_System.charset.contains(cs)

  override def newDecoder(): CharsetDecoder =
    Standard_System.charset.newDecoder

  override def newEncoder(): CharsetEncoder =
    Standard_System.charset.newEncoder
}


class Isabelle_Charset_Provider extends CharsetProvider
{
  override def charsetForName(name: String): Charset =
  {
    if (name.equalsIgnoreCase(Isabelle_Charset.name)) Isabelle_Charset.charset
    else null
  }

  override def charsets(): java.util.Iterator[Charset] =
  {
    import scala.collection.JavaConversions._
    Iterator(Isabelle_Charset.charset)
  }
}

