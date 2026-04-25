/*  Title:      Pure/General/message_digest.scala
    Author:     Makarius

Support for message digests: SHA1, SHA256.
*/

package isabelle


import java.io.{File => JFile, FileInputStream}
import java.security.MessageDigest
import java.util.HexFormat
import java.math.BigInteger


object Message_Digest {
  /* generic operations */

  final class T private[isabelle](val prefix: String, val rep: String) {
    def kind: String = Library.try_unsuffix(":", prefix).get
    def rep_short: String = rep.take(12)

    def print: String = prefix + rep
    def print_short: String = prefix + rep_short
    override def toString: String = print_short

    override def hashCode: Int = rep.hashCode
    override def equals(that: Any): Boolean =
      that match {
        case other: T => rep == other.rep
        case _ => false
      }
    def base64: String = Base64.encode(HexFormat.of().nn.parseHex(rep).nn)
  }

  object Ordering extends scala.math.Ordering[T] {
    def compare(dig1: T, dig2: T): Int = dig1.rep compare dig2.rep
  }

  abstract class Ops private[isabelle](val kind: String, val digest_length: Int) {
    val prefix: String = kind + ":"
    def print_length: Int = prefix.length + digest_length

    def fake(rep: String): T = Message_Digest.fake(prefix, rep)

    def make(update: MessageDigest => Unit): T = {
      val dig = MessageDigest.getInstance(kind).nn
      update(dig)
      val res = dig.digest().nn

      val n = dig.getDigestLength * 2
      assert(n == digest_length)
      new T(prefix, Library.format("%0" + n + "x", new BigInteger(1, res)))
    }

    val digest_empty: T = make(_ => ())

    def digest(file: JFile): T =
      make(dig => using(new FileInputStream(file)) { stream =>
        val buf = new Array[Byte](65536)
        var m = 0
        while ({
          m = stream.read(buf, 0, buf.length)
          if (m != -1) dig.update(buf, 0, m)
          m != -1
        }) ()
      })

    def digest(path: Path): T = digest(path.file)
    def digest(bytes: Array[Byte]): T = make(_.update(bytes))
    def digest(bytes: Array[Byte], offset: Int, length: Int): T =
      make(_.update(bytes, offset, length))
    def digest(string: String): T = digest(UTF8.bytes(string))

    def digest(shasum: Shasum): T = {
      shasum.rep match {
        case List(s)
        if s.length == digest_length && s.forall(Symbol.is_ascii_hex) => fake(s)
        case _ => digest(shasum.toString)
      }
    }

    def digest(bytes: Bytes): Message_Digest.T
  }

  /* particular instances */

  private lazy val instances = List(SHA1, SHA256)

  def fake(prefix: String, rep: String): T =
    instances.find(dig => dig.prefix == prefix) match {
      case None => error("Bad message digest prefix " + quote(prefix))
      case Some(dig) =>
        val m = rep.length
        val n = dig.digest_length
        if (m == n) new T(prefix, rep)
        else error("Bad message digest length " + m + " for " + quote(prefix))
    }

  def fake_prefix(s: String): T =
    instances.find(dig => s.startsWith(dig.prefix)) match {
      case None => error("Cannot determine message digest prefix from " + quote(s))
      case Some(dig) => fake(dig.prefix, Library.try_unprefix(dig.prefix, s).get)
    }
}

object SHA1 extends Message_Digest.Ops("SHA1", 40) {
  override def digest(bytes: Bytes): Message_Digest.T = bytes.sha1_digest

  object Scala_Fun extends Scala.Fun_Bytes("SHA1.digest") {
    val here = Scala_Project.here
    def apply(bytes: Bytes): Bytes = Bytes(bytes.sha1_digest.rep)
  }
}

object SHA256 extends Message_Digest.Ops("SHA256", 64) {
  override def digest(bytes: Bytes): Message_Digest.T = bytes.sha256_digest

  object Scala_Fun extends Scala.Fun_Bytes("SHA256.digest") {
    val here = Scala_Project.here
    def apply(bytes: Bytes): Bytes = Bytes(bytes.sha256_digest.rep)
  }
}
