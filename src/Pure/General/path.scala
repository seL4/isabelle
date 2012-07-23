/*  Title:      Pure/General/path.scala
    Author:     Makarius

Algebra of file-system paths: basic POSIX notation, extended by named
roots (e.g. //foo) and variables (e.g. $BAR).
*/

package isabelle


import java.io.{File => JFile}

import scala.util.matching.Regex


object Path
{
  /* path elements */

  sealed abstract class Elem
  private case class Root(val name: String) extends Elem
  private case class Basic(val name: String) extends Elem
  private case class Variable(val name: String) extends Elem
  private case object Parent extends Elem

  private def err_elem(msg: String, s: String): Nothing =
    error (msg + " path element specification: " + quote(s))

  private def check_elem(s: String): String =
    if (s == "" || s == "~" || s == "~~") err_elem("Illegal", s)
    else
      s.iterator.filter(c =>
          c == '/' || c == '\\' || c == '$' || c == ':' || c == '"' || c == '\'').toList match {
        case Nil => s
        case bads =>
          err_elem ("Illegal character(s) " + commas_quote(bads.map(_.toString)) + " in", s)
      }

  private def root_elem(s: String): Elem = Root(check_elem(s))
  private def basic_elem(s: String): Elem = Basic(check_elem(s))
  private def variable_elem(s: String): Elem = Variable(check_elem(s))

  private def apply_elem(y: Elem, xs: List[Elem]): List[Elem] =
    (y, xs) match {
      case (Root(_), _) => List(y)
      case (Parent, Root(_) :: _) => xs
      case (Parent, Basic(_) :: rest) => rest
      case _ => y :: xs
    }

  private def norm_elems(elems: List[Elem]): List[Elem] =
    (elems :\ (Nil: List[Elem]))(apply_elem)

  private def implode_elem(elem: Elem): String =
    elem match {
      case Root("") => ""
      case Root(s) => "//" + s
      case Basic(s) => s
      case Variable(s) => "$" + s
      case Parent => ".."
    }


  /* path constructors */

  val current: Path = new Path(Nil)
  val root: Path = new Path(List(Root("")))
  def named_root(s: String): Path = new Path(List(root_elem(s)))
  def basic(s: String): Path = new Path(List(basic_elem(s)))
  def variable(s: String): Path = new Path(List(variable_elem(s)))
  val parent: Path = new Path(List(Parent))


  /* explode */

  private def explode_elem(s: String): Elem =
    if (s == "..") Parent
    else if (s == "~") Variable("USER_HOME")
    else if (s == "~~") Variable("ISABELLE_HOME")
    else if (s.startsWith("$")) variable_elem(s.substring(1))
    else basic_elem(s)

  private def explode_elems(ss: List[String]): List[Elem] =
    ss.filterNot(s => s.isEmpty || s == ".").map(explode_elem).reverse

  def explode(str: String): Path =
  {
    val ss = space_explode('/', str)
    val r = ss.takeWhile(_.isEmpty).length
    val es = ss.dropWhile(_.isEmpty)
    val (roots, raw_elems) =
      if (r == 0) (Nil, es)
      else if (r == 1) (List(Root("")), es)
      else if (es.isEmpty) (List(Root("")), Nil)
      else (List(root_elem(es.head)), es.tail)
    new Path(norm_elems(explode_elems(raw_elems) ++ roots))
  }

  def split(str: String): List[Path] =
    space_explode(':', str).filterNot(_.isEmpty).map(explode)


  /* encode */

  val encode: XML.Encode.T[Path] = (path => XML.Encode.string(path.implode))
}


final class Path private(private val elems: List[Path.Elem]) // reversed elements
{
  def is_current: Boolean = elems.isEmpty
  def is_absolute: Boolean = !elems.isEmpty && elems.last.isInstanceOf[Path.Root]
  def is_basic: Boolean = elems match { case List(Path.Basic(_)) => true case _ => false }

  def +(other: Path): Path = new Path((other.elems :\ elems)(Path.apply_elem))


  /* implode */

  def implode: String =
    elems match {
      case Nil => "."
      case List(Path.Root("")) => "/"
      case _ => elems.map(Path.implode_elem).reverse.mkString("/")
    }

  override def toString: String = quote(implode)


  /* base element */

  private def split_path: (Path, String) =
    elems match {
      case Path.Basic(s) :: xs => (new Path(xs), s)
      case _ => error("Cannot split path into dir/base: " + toString)
    }

  def dir: Path = split_path._1
  def base: Path = new Path(List(Path.Basic(split_path._2)))

  def ext(e: String): Path =
    if (e == "") this
    else {
      val (prfx, s) = split_path
      prfx + Path.basic(s + "." + e)
    }

  private val Ext = new Regex("(.*)\\.([^.]*)")

  def split_ext: (Path, String) =
  {
    val (prefix, base) = split_path
    base match {
      case Ext(b, e) => (prefix + Path.basic(b), e)
      case _ => (Path.basic(base), "")
    }
  }


  /* expand */

  def expand: Path =
  {
    def eval(elem: Path.Elem): List[Path.Elem] =
      elem match {
        case Path.Variable(s) =>
          Path.explode(Isabelle_System.getenv_strict(s)).elems
        case x => List(x)
      }

    new Path(Path.norm_elems(elems.map(eval).flatten))
  }


  /* platform file */

  def file: JFile = Isabelle_System.platform_file(this)
}
