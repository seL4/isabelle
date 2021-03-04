/*  Title:      Pure/Thy/latex.scala
    Author:     Makarius

Support for LaTeX.
*/

package isabelle


import java.io.{File => JFile}

import scala.annotation.tailrec
import scala.util.matching.Regex


object Latex
{
  /** latex errors **/

  def latex_errors(dir: Path, root_name: String): List[String] =
  {
    val root_log_path = dir + Path.explode(root_name).ext("log")
    if (root_log_path.is_file) {
      for { (msg, pos) <- filter_errors(dir, File.read(root_log_path)) }
      yield "Latex error" + Position.here(pos) + ":\n" + Library.prefix_lines("  ", msg)
    }
    else Nil
  }


  /* generated .tex file */

  private val File_Pattern = """^%:%file=(.+)%:%$""".r
  private val Line_Pattern = """^*%:%(\d+)=(\d+)%:%$""".r

  def read_tex_file(tex_file: Path): Tex_File =
  {
    val positions =
      Line.logical_lines(File.read(tex_file)).reverse.
        takeWhile(_ != "\\endinput").reverse

    val source_file =
      positions match {
        case File_Pattern(file) :: _ => Some(file)
        case _ => None
      }

    val source_lines =
      if (source_file.isEmpty) Nil
      else
        positions.flatMap(line =>
          line match {
            case Line_Pattern(Value.Int(line), Value.Int(source_line)) => Some(line -> source_line)
            case _ => None
          })

    new Tex_File(tex_file, source_file, source_lines)
  }

  final class Tex_File private[Latex](
    tex_file: Path, source_file: Option[String], source_lines: List[(Int, Int)])
  {
    override def toString: String = tex_file.toString

    def source_position(l: Int): Option[Position.T] =
      source_file match {
        case None => None
        case Some(file) =>
          val source_line =
            source_lines.iterator.takeWhile({ case (m, _) => m <= l }).
              foldLeft(0) { case (_, (_, n)) => n }
          if (source_line == 0) None else Some(Position.Line_File(source_line, file))
      }

    def position(line: Int): Position.T =
      source_position(line) getOrElse Position.Line_File(line, tex_file.implode)
  }


  /* latex log */

  def filter_errors(dir: Path, root_log: String): List[(String, Position.T)] =
  {
    val seen_files = Synchronized(Map.empty[JFile, Tex_File])

    def check_tex_file(path: Path): Option[Tex_File] =
      seen_files.change_result(seen =>
        seen.get(path.file) match {
          case None =>
            if (path.is_file) {
              val tex_file = read_tex_file(path)
              (Some(tex_file), seen + (path.file -> tex_file))
            }
            else (None, seen)
          case some => (some, seen)
        })

    def tex_file_position(path: Path, line: Int): Position.T =
      check_tex_file(path) match {
        case Some(tex_file) => tex_file.position(line)
        case None => Position.Line_File(line, path.implode)
      }

    object File_Line_Error
    {
      val Pattern: Regex = """^(.*?\.\w\w\w):(\d+): (.*)$""".r
      def unapply(line: String): Option[(Path, Int, String)] =
        line match {
          case Pattern(file, Value.Int(line), message) =>
            val path = File.standard_path(file)
            if (Path.is_wellformed(path)) {
              val file = (dir + Path.explode(path)).canonical
              val msg = Library.perhaps_unprefix("LaTeX Error: ", message)
              if (file.is_file) Some((file, line, msg)) else None
            }
            else None
          case _ => None
        }
    }

    val Line_Error = """^l\.\d+ (.*)$""".r
    val More_Error =
      List(
        "<argument>",
        "<template>",
        "<recently read>",
        "<to be read again>",
        "<inserted text>",
        "<output>",
        "<everypar>",
        "<everymath>",
        "<everydisplay>",
        "<everyhbox>",
        "<everyvbox>",
        "<everyjob>",
        "<everycr>",
        "<mark>",
        "<everyeof>",
        "<write>").mkString("^(?:", "|", ") (.*)$").r

    val Bad_File = """^! LaTeX Error: (File `.*' not found\.)$""".r

    val error_ignore =
      Set(
        "See the LaTeX manual or LaTeX Companion for explanation.",
        "Type  H <return>  for immediate help.")

    def error_suffix1(lines: List[String]): Option[String] =
    {
      val lines1 =
        lines.take(20).takeWhile({ case File_Line_Error((_, _, _)) => false case _ => true })
      lines1.zipWithIndex.collectFirst({
        case (Line_Error(msg), i) =>
          cat_lines(lines1.take(i).filterNot(error_ignore) ::: List(msg)) })
    }
    def error_suffix2(lines: List[String]): Option[String] =
      lines match {
        case More_Error(msg) :: _ => Some(msg)
        case _ => None
      }

    @tailrec def filter(lines: List[String], result: List[(String, Position.T)])
      : List[(String, Position.T)] =
    {
      lines match {
        case File_Line_Error((file, line, msg1)) :: rest1 =>
          val pos = tex_file_position(file, line)
          val msg2 = error_suffix1(rest1) orElse error_suffix2(rest1) getOrElse ""
          filter(rest1, (Exn.cat_message(msg1, msg2), pos) :: result)
        case Bad_File(msg) :: rest =>
          filter(rest, (msg, Position.none) :: result)
        case _ :: rest => filter(rest, result)
        case Nil => result.reverse
      }
    }

    filter(Line.logical_lines(root_log), Nil)
  }
}
