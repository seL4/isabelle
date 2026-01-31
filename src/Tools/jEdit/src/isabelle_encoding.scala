/*  Title:      Tools/jEdit/src/isabelle_encoding.scala
    Author:     Makarius

Isabelle encoding -- based on UTF-8.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.io.Encoding

import java.nio.charset.{CodingErrorAction, CharacterCodingException}
import java.io.{InputStream, OutputStream, Reader, Writer, OutputStreamWriter,
  CharArrayReader, ByteArrayOutputStream}

import scala.io.{Codec, BufferedSource}


object Isabelle_Encoding {
  val NAME = "UTF-8-Isabelle"

  def is_active(buffer: JEditBuffer): Boolean =
    buffer.getStringProperty(JEditBuffer.ENCODING).asInstanceOf[String] == NAME

  def gui_style(buffer: JEditBuffer): GUI.Style_Symbol =
    GUI.Style_Symbol_Recoded(is_active(buffer))
}

class Isabelle_Encoding extends Encoding {
  private val BUFSIZE = 32768

  private def text_reader(in: InputStream, codec: Codec, strict: Boolean): Reader = {
    val source = (new BufferedSource(in)(codec)).mkString

    if (strict && Codepoint.iterator(source).exists(Symbol.symbols.code_defined))
      throw new CharacterCodingException()

    new CharArrayReader(Symbol.decode(source).toArray)
  }

  override def getTextReader(in: InputStream): Reader =
    text_reader(in, Codec(UTF8.charset), true)

  override def getPermissiveTextReader(in: InputStream): Reader = {
    val codec = Codec(UTF8.charset)
    codec.onMalformedInput(CodingErrorAction.REPLACE)
    codec.onUnmappableCharacter(CodingErrorAction.REPLACE)
    text_reader(in, codec, false)
  }

  override def getTextWriter(out: OutputStream): Writer = {
    val buffer = new ByteArrayOutputStream(BUFSIZE) {
      override def flush(): Unit = {
        val text = Symbol.encode(toString(UTF8.charset))
        out.write(UTF8.bytes(text))
        out.flush()
      }
      override def close(): Unit = out.close()
    }
    new OutputStreamWriter(buffer, UTF8.charset.newEncoder())
  }
}
