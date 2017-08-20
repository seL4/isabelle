/*  Title:      Tools/jEdit/src/isabelle_encoding.scala
    Author:     Makarius

Isabelle encoding -- based on UTF-8.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.buffer.JEditBuffer


object Isabelle_Encoding
{
  def is_active(buffer: JEditBuffer): Boolean =
    buffer.getStringProperty(JEditBuffer.ENCODING).asInstanceOf[String] == "UTF-8-Isabelle"

  def maybe_decode(buffer: JEditBuffer, s: String): String =
    if (is_active(buffer)) Symbol.decode(s) else s
}
