/*  Title:      Pure/General/sha1.scala
    Author:     Makarius

Digest strings according to SHA-1 (see RFC 3174).
*/

package isabelle


import java.io.{File => JFile, FileInputStream}
import java.security.MessageDigest
import java.util.Locale
import java.math.BigInteger


object SHA1
{
  final class Digest private[SHA1](val rep: String)
  {
    override def hashCode: Int = rep.hashCode
    override def equals(that: Any): Boolean =
      that match {
        case other: Digest => rep == other.rep
        case _ => false
      }
    override def toString: String = rep
  }

  private def sha1_digest(sha: MessageDigest): Digest =
    new Digest(String.format(Locale.ROOT, "%040x", new BigInteger(1, sha.digest())))

  def fake(rep: String): Digest = new Digest(rep)

  def digest(file: JFile): Digest =
  {
    val digest = MessageDigest.getInstance("SHA")

    using(new FileInputStream(file))(stream =>
    {
      val buf = new Array[Byte](65536)
      var m = 0
      do {
        m = stream.read(buf, 0, buf.length)
        if (m != -1) digest.update(buf, 0, m)
      } while (m != -1)
    })

    sha1_digest(digest)
  }

  def digest(path: Path): Digest = digest(path.file)

  def digest(bytes: Array[Byte]): Digest =
  {
    val digest = MessageDigest.getInstance("SHA")
    digest.update(bytes)

    sha1_digest(digest)
  }

  def digest(bytes: Bytes): Digest = bytes.sha1_digest
  def digest(string: String): Digest = digest(Bytes(string))
  def digest_set(digests: List[Digest]): Digest =
    digest(cat_lines(digests.map(_.toString).sorted))

  val digest_length: Int = digest("").rep.length
}
