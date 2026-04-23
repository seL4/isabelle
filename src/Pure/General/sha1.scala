/*  Title:      Pure/General/sha1.scala
    Author:     Makarius

SHA-1 message digest according to RFC 3174.
*/

package isabelle


import java.io.{File => JFile, FileInputStream}
import java.security.MessageDigest
import java.util.HexFormat

import isabelle.setup.{Build => Setup_Build}


object SHA1 {
  /* digest */

  final class Digest private[SHA1](rep: String) {
    override def toString: String = rep
    override def hashCode: Int = rep.hashCode
    override def equals(that: Any): Boolean =
      that match {
        case other: Digest => rep == other.toString
        case _ => false
      }
    def base64: String = Base64.encode(HexFormat.of().nn.parseHex(rep).nn)
  }

  def fake_digest(rep: String): Digest = new Digest(rep)

  def make_digest(body: MessageDigest => Unit): Digest = {
    val digest_body =
      new Setup_Build.Digest_Body { def apply(sha: MessageDigest | Null): Unit = body(sha.nn) }
    new Digest(Setup_Build.make_digest(digest_body).nn)
  }

  val digest_empty: Digest = make_digest(_ => ())
  def digest_length: Int = digest_empty.toString.length

  def digest(file: JFile): Digest =
    make_digest(sha => using(new FileInputStream(file)) { stream =>
      val buf = new Array[Byte](65536)
      var m = 0
      while ({
        m = stream.read(buf, 0, buf.length)
        if (m != -1) sha.update(buf, 0, m)
        m != -1
      }) ()
    })

  def digest(path: Path): Digest = digest(path.file)
  def digest(bytes: Array[Byte]): Digest = make_digest(_.update(bytes))
  def digest(bytes: Array[Byte], offset: Int, length: Int): Digest =
    make_digest(_.update(bytes, offset, length))
  def digest(bytes: Bytes): Digest = bytes.sha1_digest
  def digest(string: String): Digest = digest(Bytes(string))

  object Scala_Fun extends Scala.Fun_Bytes("SHA1.digest") {
    val here = Scala_Project.here
    def apply(bytes: Bytes): Bytes = Bytes(bytes.sha1_digest.toString)
  }
}
