/*
 * Isabelle encoding -- based on utf-8
 *
 * @author Makarius
 */

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.io.Encoding
import org.gjt.sp.jedit.buffer.JEditBuffer

import java.nio.charset.{Charset, CodingErrorAction}
import java.io.{InputStream, OutputStream, Reader, Writer, InputStreamReader, OutputStreamWriter,
  CharArrayReader, ByteArrayOutputStream}

import scala.io.{Codec, Source, BufferedSource}


object Isabelle_Encoding
{
  val NAME = "UTF-8-Isabelle"

  def is_active(buffer: JEditBuffer): Boolean =
    buffer.getStringProperty(JEditBuffer.ENCODING).asInstanceOf[String] == NAME
}

class Isabelle_Encoding extends Encoding
{
  private val charset = Charset.forName(Standard_System.charset)
  val BUFSIZE = 32768

  private def text_reader(in: InputStream, codec: Codec): Reader =
  {
    val source = new BufferedSource(in)(codec)
    new CharArrayReader(Isabelle.system.symbols.decode(source.mkString).toArray)
  }

	override def getTextReader(in: InputStream): Reader =
    text_reader(in, Standard_System.codec())

	override def getPermissiveTextReader(in: InputStream): Reader =
	{
		val codec = Standard_System.codec()
		codec.onMalformedInput(CodingErrorAction.REPLACE)
		codec.onUnmappableCharacter(CodingErrorAction.REPLACE)
		text_reader(in, codec)
	}

  override def getTextWriter(out: OutputStream): Writer =
  {
    val buffer = new ByteArrayOutputStream(BUFSIZE) {
      override def flush()
      {
        val text = Isabelle.system.symbols.encode(toString(Standard_System.charset))
        out.write(text.getBytes(Standard_System.charset))
        out.flush()
      }
      override def close() { out.close() }
    }
		new OutputStreamWriter(buffer, charset.newEncoder())
  }
}
