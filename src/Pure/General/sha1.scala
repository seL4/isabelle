/*  Title:      Pure/General/sha1.scala
    Author:     Makarius

SHA-1 message digest according to RFC 3174.
*/

package isabelle


import java.io.{File => JFile, FileInputStream}
import java.security.MessageDigest

import isabelle.setup.{Build => Setup_Build}


object SHA1
{
  final class Digest private[SHA1](rep: String)
  {
    override def toString: String = rep
    override def hashCode: Int = rep.hashCode
    override def equals(that: Any): Boolean =
      that match {
        case other: Digest => rep == other.toString
        case _ => false
      }
    def shasum(name: String): String = rep + " " + name
  }

  def fake_digest(rep: String): Digest = new Digest(rep)

  def make_digest(body: MessageDigest => Unit): Digest =
  {
    val digest_body = new Setup_Build.Digest_Body { def apply(sha: MessageDigest): Unit = body(sha)}
    new Digest(Setup_Build.make_digest(digest_body))
  }

  def digest(file: JFile): Digest =
    make_digest(sha => using(new FileInputStream(file))(stream =>
      {
        val buf = new Array[Byte](65536)
        var m = 0
        var cont = true
        while (cont) {
          m = stream.read(buf, 0, buf.length)
          if (m != -1) sha.update(buf, 0, m)
          cont = (m != -1)
        }
      }))

  def digest(path: Path): Digest = digest(path.file)
  def digest(bytes: Array[Byte]): Digest = make_digest(_.update(bytes))
  def digest(bytes: Bytes): Digest = bytes.sha1_digest
  def digest(string: String): Digest = digest(Bytes(string))
  def digest_set(digests: List[Digest]): Digest =
    digest(cat_lines(digests.map(_.toString).sorted))

  val digest_length: Int = digest("").toString.length
}
