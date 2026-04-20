/*  Title:      Pure/General/utf8.scala
    Author:     Makarius

Variations on UTF-8.
*/

package isabelle


import java.nio.charset.{Charset, StandardCharsets}


object UTF8 {
  val charset: Charset = StandardCharsets.UTF_8.nn
  val charset_name: String = charset.name.nn

  def bytes(s: String): Array[Byte] = s.getBytes(charset).nn

  def raw_bytes(s: String): Array[Byte] = s.getBytes(StandardCharsets.ISO_8859_1).nn
}
