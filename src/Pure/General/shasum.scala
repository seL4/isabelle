/*  Title:      Pure/General/shasum.scala
    Author:     Makarius

Collections of message digests in canonical order.
*/

package isabelle

object Shasum {
  val none: Shasum = new Shasum(Nil)
  def flat(list: List[Shasum]): Shasum = new Shasum(list.flatMap(_.rep))
  def fake(text: String): Shasum = new Shasum(Library.trim_split_lines(text))

  def make(digest: SHA1.Digest, name: String): Shasum =
    new Shasum(List(digest.toString + " " + name))
  def make_meta_info(digest: SHA1.Digest): Shasum =
    make(digest, isabelle.setup.Build.META_INFO.nn)
  def make_sorted(args: List[(SHA1.Digest, String)]): Shasum =
    flat(args.sortBy(_._2).map(make))
}

final class Shasum private(private val rep: List[String]) {
  override def equals(other: Any): Boolean =
    other match {
      case that: Shasum => rep.equals(that.rep)
      case _ => false
    }
  override def hashCode: Int = rep.hashCode
  override def toString: String = Library.terminate_lines(rep)

  def print(indent: Int = 0): String =
    Library.indent_lines(indent,
      proper_string(Library.trim_line(toString)).getOrElse("<empty>"))

  def is_empty: Boolean = rep.isEmpty

  def diff(other: Shasum): Option[(Shasum, Shasum)] =
    if (this == other) None
    else {
      val a = rep.filterNot(other.rep.toSet.contains)
      val b = other.rep.filterNot(rep.toSet.contains)
      Some((new Shasum(a), new Shasum(b)))
    }

  def :::(other: Shasum): Shasum = new Shasum(other.rep ::: rep)

  def filter(pred: String => Boolean): Shasum = new Shasum(rep.filter(pred))

  def digest: SHA1.Digest = {
    rep match {
      case List(s)
      if s.length == SHA1.digest_length && s.forall(Symbol.is_ascii_hex) => SHA1.fake_digest(s)
      case _ => SHA1.digest(toString)
    }
  }
}
