/*  Title:      Pure/General/sha1.scala
    Module:     PIDE
    Author:     Makarius

Digest strings according to SHA-1 (see RFC 3174).
*/

package isabelle


import java.io.{File => JFile, FileInputStream}
import java.security.MessageDigest


object SHA1
{
  sealed case class Digest(rep: String)
  {
    override def toString: String = rep
  }

  private def make_result(digest: MessageDigest): Digest =
  {
    val result = new StringBuilder
    for (b <- digest.digest()) {
      val i = b.asInstanceOf[Int] & 0xFF
      if (i < 16) result += '0'
      result ++= Integer.toHexString(i)
    }
    Digest(result.toString)
  }

  def digest(file: JFile): Digest =
  {
    val stream = new FileInputStream(file)
    val digest = MessageDigest.getInstance("SHA")

    val buf = new Array[Byte](65536)
    var m = 0
    try {
      do {
        m = stream.read(buf, 0, buf.length)
        if (m != -1) digest.update(buf, 0, m)
      } while (m != -1)
    }
    finally { stream.close }

    make_result(digest)
  }

  def digest(path: Path): Digest = digest(path.file)

  def digest(bytes: Array[Byte]): Digest =
  {
    val digest = MessageDigest.getInstance("SHA")
    digest.update(bytes)

    make_result(digest)
  }

  def digest(string: String): Digest = digest(Standard_System.string_bytes(string))
}

