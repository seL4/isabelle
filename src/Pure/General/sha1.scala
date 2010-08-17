/*  Title:      Pure/General/sha1.scala
    Author:     Makarius

Digesting strings according to SHA-1 (see RFC 3174).
*/

package isabelle


import java.security.MessageDigest


object SHA1
{
  def digest_bytes(bytes: Array[Byte]): String =
  {
    val result = new StringBuilder
    for (b <- MessageDigest.getInstance("SHA").digest(bytes)) {
      val i = b.asInstanceOf[Int] & 0xFF
      if (i < 16) result += '0'
      result ++= Integer.toHexString(i)
    }
    result.toString
  }

  def digest(s: String): String = digest_bytes(Standard_System.string_bytes(s))
}

