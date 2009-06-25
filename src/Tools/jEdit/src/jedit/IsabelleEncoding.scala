/*
 * Isabelle encoding -- based on utf-8
 *
 * @author Makarius
 */

package isabelle.jedit

import org.gjt.sp.jedit.io.Encoding

import java.nio.charset.{Charset, CodingErrorAction}
import java.io.{InputStream, OutputStream, Reader, Writer, InputStreamReader, OutputStreamWriter}


class IsabelleEncoding extends Encoding
{
  private val charset = Charset.forName(Isabelle_System.charset)

	override def getTextReader(in: InputStream): Reader =
		new InputStreamReader(in, charset.newDecoder())

	override def getTextWriter(out: OutputStream): Writer =
		new OutputStreamWriter(out, charset.newEncoder())

	override def getPermissiveTextReader(in: InputStream): Reader =
	{
		val decoder = charset.newDecoder()
		decoder.onMalformedInput(CodingErrorAction.REPLACE)
		decoder.onUnmappableCharacter(CodingErrorAction.REPLACE)
		new InputStreamReader(in, decoder)
	}
}
