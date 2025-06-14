/*  Title:      Pure/General/path.scala
    Author:     Makarius

Algebra of file-system paths: basic POSIX notation, extended by named
roots (e.g. //foo) and variables (e.g. $BAR).
*/

package isabelle


import java.io.{File => JFile}
import java.nio.file.{Path => JPath}

import scala.util.matching.Regex


object Path {
  /* path elements */

  sealed abstract class Elem
  private case class Root(name: String) extends Elem
  private case class Basic(name: String) extends Elem
  private case class Variable(name: String) extends Elem
  private case object Parent extends Elem

  private def err_elem(msg: String, s: String): Nothing =
    error(msg + " path element " + quote(s))

  private val illegal_elem = Set("", "~", "~~", ".", "..")
  private val illegal_char = "/\\$:\"'<>|?*"

  private def check_elem(s: String): String =
    if (illegal_elem.contains(s)) err_elem("Illegal", s)
    else {
      for (c <- s) {
        if (c.toInt < 32)
          err_elem("Illegal control character " + c.toInt + " in", s)
        if (illegal_char.contains(c))
          err_elem("Illegal character " + quote(c.toString) + " in", s)
      }
      s
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
    elems.foldRight(List.empty[Elem])(apply_elem)

  private def implode_elem(elem: Elem, short: Boolean): String =
    elem match {
      case Root("") => ""
      case Root(s) => "//" + s
      case Basic(s) => s
      case Variable("USER_HOME") if short => "~"
      case Variable("ISABELLE_HOME") if short => "~~"
      case Variable(s) => "$" + s
      case Parent => ".."
    }

  private def squash_elem(elem: Elem): String =
    elem match {
      case Root("") => "ROOT"
      case Root(s) => "SERVER_" + s
      case Basic(s) => s
      case Variable(s) => s
      case Parent => "PARENT"
    }


  /* path constructors */

  val current: Path = new Path(Nil)
  val root: Path = new Path(List(Root("")))
  def named_root(s: String): Path = new Path(List(root_elem(s)))
  def make(elems: List[String]): Path = new Path(elems.reverse.map(basic_elem))
  def basic(s: String): Path = new Path(List(basic_elem(s)))
  def variable(s: String): Path = new Path(List(variable_elem(s)))
  val parent: Path = new Path(List(Parent))

  val USER_HOME: Path = variable("USER_HOME")
  val ISABELLE_HOME: Path = variable("ISABELLE_HOME")

  val index_html: Path = basic("index.html")


  /* explode */

  def explode(str: String): Path = {
    def explode_elem(s: String): Elem =
      try {
        if (s == "..") Parent
        else if (s == "~") Variable("USER_HOME")
        else if (s == "~~") Variable("ISABELLE_HOME")
        else if (s.startsWith("$")) variable_elem(s.substring(1))
        else basic_elem(s)
      }
      catch { case ERROR(msg) => cat_error(msg, "The error(s) above occurred in " + quote(str)) }
  
    val ss = space_explode('/', str)
    val r = ss.takeWhile(_.isEmpty).length
    val es = ss.dropWhile(_.isEmpty)
    val (roots, raw_elems) =
      if (r == 0) (Nil, es)
      else if (r == 1) (List(Root("")), es)
      else if (es.isEmpty) (List(Root("")), Nil)
      else (List(root_elem(es.head)), es.tail)
    val elems = raw_elems.filterNot(s => s.isEmpty || s == ".").map(explode_elem)

    new Path(norm_elems(elems reverse_::: roots))
  }

  def is_wellformed(str: String): Boolean =
    try { explode(str); true } catch { case ERROR(_) => false }

  def is_valid(str: String): Boolean =
    try { explode(str).expand; true } catch { case ERROR(_) => false }

  def split(str: String): List[Path] =
    space_explode(':', str).filterNot(_.isEmpty).map(explode)

  def split_permissive(str: String): List[(Path, Boolean)] =
    space_explode(':', str).flatMap(
      {
        case "" | "?" => None
        case s =>
          Library.try_unsuffix("?", s) match {
            case None => Some(explode(s) -> false)
            case Some(p) => Some(explode(p) -> true)
          }
      })

  def split_permissive_files(str: String): List[Path] =
    for {
      (path, permissive) <- split_permissive(str)
      if !permissive || path.is_file
    } yield path


  /* encode */

  val encode: XML.Encode.T[Path] = (path => XML.Encode.string(path.implode))


  /* reserved names */

  private val reserved_windows: Set[String] =
    Set("CON", "PRN", "AUX", "NUL",
      "COM1", "COM2", "COM3", "COM4", "COM5", "COM6", "COM7", "COM8", "COM9",
      "LPT1", "LPT2", "LPT3", "LPT4", "LPT5", "LPT6", "LPT7", "LPT8", "LPT9")

  def is_reserved(name: String): Boolean =
    Long_Name.explode(name).exists(a => reserved_windows.contains(Word.uppercase(a)))


  /* case-insensitive names */

  def check_case_insensitive(paths: List[Path]): Unit = {
    val table =
      paths.foldLeft(Multi_Map.empty[String, String]) { case (tab, path) =>
        val name = path.expand.implode
        tab.insert(Word.lowercase(name), name)
      }
    val collisions =
      (for { (_, coll) <- table.iterator_list if coll.length > 1 } yield coll).toList.flatten
    if (collisions.nonEmpty) {
      error(("Collision of file names due case-insensitivity:" :: collisions).mkString("\n  "))
    }
  }

  def eq_case_insensitive(path1: Path, path2: Path): Boolean =
    path1 == path2 ||
    Word.lowercase(path1.expand.implode) == Word.lowercase(path2.expand.implode)
}


final class Path private(
  protected val elems: List[Path.Elem]  // reversed elements
) {
  override def hashCode: Int = elems.hashCode
  override def equals(that: Any): Boolean =
    that match {
      case other: Path => elems == other.elems
      case _ => false
    }

  def is_current: Boolean = elems.isEmpty
  def is_absolute: Boolean = elems.nonEmpty && elems.last.isInstanceOf[Path.Root]
  def is_root: Boolean = elems match { case List(Path.Root(_)) => true case _ => false }
  def is_basic: Boolean = elems match { case List(Path.Basic(_)) => true case _ => false }
  def all_basic: Boolean = elems.forall(_.isInstanceOf[Path.Basic])
  def starts_basic: Boolean = elems.nonEmpty && elems.last.isInstanceOf[Path.Basic]

  def +(other: Path): Path = new Path(other.elems.foldRight(elems)(Path.apply_elem))


  /* implode */

  private def gen_implode(short: Boolean): String =
    elems match {
      case Nil => "."
      case List(Path.Root("")) => "/"
      case _ => elems.map(Path.implode_elem(_, short)).reverse.mkString("/")
    }
  def implode: String = gen_implode(false)
  def implode_short: String = gen_implode(true)

  override def toString: String = quote(implode)


  /* base element */

  private def split_path: (Path, String) =
    elems match {
      case Path.Basic(s) :: xs => (new Path(xs), s)
      case _ => error("Cannot split path into dir/base: " + toString)
    }

  def dir: Path = split_path._1
  def base: Path = new Path(List(Path.Basic(split_path._2)))

  def ends_with(a: String): Boolean =
    elems match {
      case Path.Basic(b) :: _ => b.endsWith(a)
      case _ => false
    }
  def is_java: Boolean = ends_with(".java")
  def is_scala: Boolean = ends_with(".scala")
  def is_pdf: Boolean = ends_with(".pdf")
  def is_latex: Boolean =
    ends_with(".tex") ||
    ends_with(".sty") ||
    ends_with(".cls") ||
    ends_with(".clo")

  def ext(e: String): Path =
    if (e == "") this
    else {
      val (prfx, s) = split_path
      prfx + Path.basic(s + "." + e)
    }

  def bib: Path = ext("bib")
  def blg: Path = ext("blg")
  def db: Path = ext("db")
  def gz: Path = ext("gz")
  def html: Path = ext("html")
  def jar: Path = ext("jar")
  def json: Path = ext("json")
  def log: Path = ext("log")
  def orig: Path = ext("orig")
  def patch: Path = ext("patch")
  def pdf: Path = ext("pdf")
  def shasum: Path = ext("shasum")
  def tar: Path = ext("tar")
  def tex: Path = ext("tex")
  def thy: Path = ext("thy")
  def xml: Path = ext("xml")
  def xz: Path = ext("xz")
  def zip: Path = ext("zip")
  def zst: Path = ext("zst")

  def backup: Path = {
    val (prfx, s) = split_path
    prfx + Path.basic(s + "~")
  }

  def backup2: Path = {
    val (prfx, s) = split_path
    prfx + Path.basic(s + "~~")
  }

  def exe: Path = ext("exe")
  def exe_if(b: Boolean): Path = if (b) exe else this
  def platform_exe: Path = exe_if(Platform.is_windows)

  private val Ext = new Regex("(.*)\\.([^.]*)")

  def split_ext: (Path, String) = {
    val (prefix, base) = split_path
    base match {
      case Ext(b, e) => (prefix + Path.basic(b), e)
      case _ => (prefix + Path.basic(base), "")
    }
  }

  def drop_ext: Path = split_ext._1
  def get_ext: String = split_ext._2

  def squash: Path = new Path(elems.map(elem => Path.Basic(Path.squash_elem(elem))))


  /* expand */

  def expand_env(env: Isabelle_System.Settings): Path = {
    def eval(elem: Path.Elem): List[Path.Elem] =
      elem match {
        case Path.Variable(s) =>
          val path = Path.explode(Isabelle_System.getenv_strict(s, env))
          if (path.elems.exists(_.isInstanceOf[Path.Variable]))
            error("Illegal path variable nesting: " + Properties.Eq(s, path.toString))
          else path.elems
        case x => List(x)
      }

    new Path(Path.norm_elems(elems.flatMap(eval)))
  }

  def expand: Path = expand_env(Isabelle_System.Settings())

  def file_name: String = expand.base.implode


  /* platform files */

  def file: JFile = File.platform_file(this)

  def is_file: Boolean = file.isFile
  def is_dir: Boolean = file.isDirectory

  def check_file: Path = if (is_file) this else error("No such file: " + this.expand)
  def check_dir: Path = if (is_dir) this else error("No such directory: " + this.expand)

  def java_path: JPath = file.toPath

  def absolute_file: JFile = File.absolute(file)
  def canonical_file: JFile = File.canonical(file)

  def absolute: Path = File.path(absolute_file)
  def canonical: Path = File.path(canonical_file)
}
