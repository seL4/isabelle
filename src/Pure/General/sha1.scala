/*  Title:      Pure/General/sha1.scala
    Module:     PIDE
    Author:     Makarius

Digest strings according to SHA-1 (see RFC 3174).
*/

package isabelle


import java.security.MessageDigest


object SHA1
{
  sealed case class Digest(rep: String)
  {
    override def toString: String = rep
  }

  def digest_bytes(bytes: Array[Byte]): Digest =
  {
    val result = new StringBuilder
    for (b <- MessageDigest.getInstance("SHA").digest(bytes)) {
      val i = b.asInstanceOf[Int] & 0xFF
      if (i < 16) result += '0'
      result ++= Integer.toHexString(i)
    }
    Digest(result.toString)
  }

  def digest(s: String): Digest = digest_bytes(Standard_System.string_bytes(s))
}

