/*  Title:      Pure/General/utf8.scala
    Author:     Makarius

Variations on UTF-8.
*/

package isabelle


import java.nio.charset.{Charset, StandardCharsets}


object UTF8 {
  val charset: Charset = StandardCharsets.UTF_8

  def bytes(s: String): Array[Byte] = s.getBytes(charset)
}
