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
    def base64: String = Base64.encode(HexFormat.of().parseHex(rep))
  }

  def fake_digest(rep: String): Digest = new Digest(rep)

  def make_digest(body: MessageDigest => Unit): Digest = {
    val digest_body = new Setup_Build.Digest_Body { def apply(sha: MessageDigest): Unit = body(sha)}
    new Digest(Setup_Build.make_digest(digest_body))
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


  /* shasum */

  final class Shasum private[SHA1](private[SHA1] val rep: List[String]) {
    override def equals(other: Any): Boolean =
      other match {
        case that: Shasum => rep.equals(that.rep)
        case _ => false
      }
    override def hashCode: Int = rep.hashCode
    override def toString: String = Library.terminate_lines(rep)

    def is_empty: Boolean = rep.isEmpty

    def - (other: Shasum): Shasum = new Shasum(rep.filterNot(other.rep.toSet.contains))

    def :::(other: Shasum): Shasum = new Shasum(other.rep ::: rep)

    def filter(pred: String => Boolean): Shasum = new Shasum(rep.filter(pred))

    def digest: Digest = {
      rep match {
        case List(s)
        if s.length == digest_length && s.forall(Symbol.is_ascii_hex) => fake_digest(s)
        case _ => SHA1.digest(toString)
      }
    }
  }

  val no_shasum: Shasum = new Shasum(Nil)
  def flat_shasum(list: List[Shasum]): Shasum = new Shasum(list.flatMap(_.rep))
  def fake_shasum(text: String): Shasum = new Shasum(Library.trim_split_lines(text))

  def shasum(digest: Digest, name: String): Shasum =
    new Shasum(List(digest.toString + " " + name))
  def shasum_meta_info(digest: Digest): Shasum =
    shasum(digest, isabelle.setup.Build.META_INFO)
  def shasum_sorted(args: List[(Digest, String)]): Shasum =
    flat_shasum(args.sortBy(_._2).map(shasum))
}
