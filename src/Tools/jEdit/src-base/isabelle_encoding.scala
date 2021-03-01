/*  Title:      Tools/jEdit/src-base/isabelle_encoding.scala
    Author:     Makarius

Isabelle encoding -- based on UTF-8.
*/

package isabelle.jedit_base


import isabelle._

import org.gjt.sp.jedit.io.Encoding

import java.nio.charset.{Charset, CodingErrorAction, CharacterCodingException}
import java.io.{InputStream, OutputStream, Reader, Writer, InputStreamReader, OutputStreamWriter,
  CharArrayReader, ByteArrayOutputStream}

import scala.io.{Codec, BufferedSource}


class Isabelle_Encoding extends Encoding
{
  private val BUFSIZE = 32768

  private def text_reader(in: InputStream, codec: Codec, strict: Boolean): Reader =
  {
    val source = (new BufferedSource(in)(codec)).mkString

    if (strict && Codepoint.iterator(source).exists(Symbol.is_code))
      throw new CharacterCodingException()

    new CharArrayReader(Symbol.decode(source).toArray)
  }

  override def getTextReader(in: InputStream): Reader =
    text_reader(in, UTF8.codec(), true)

  override def getPermissiveTextReader(in: InputStream): Reader =
  {
    val codec = UTF8.codec()
    codec.onMalformedInput(CodingErrorAction.REPLACE)
    codec.onUnmappableCharacter(CodingErrorAction.REPLACE)
    text_reader(in, codec, false)
  }

  override def getTextWriter(out: OutputStream): Writer =
  {
    val buffer = new ByteArrayOutputStream(BUFSIZE) {
      override def flush(): Unit =
      {
        val text = Symbol.encode(toString(UTF8.charset_name))
        out.write(UTF8.bytes(text))
        out.flush()
      }
      override def close(): Unit = out.close()
    }
    new OutputStreamWriter(buffer, UTF8.charset.newEncoder())
  }
}
