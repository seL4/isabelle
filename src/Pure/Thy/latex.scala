/*  Title:      Pure/Thy/latex.scala
    Author:     Makarius

Support for LaTeX.
*/

package isabelle


import java.io.{File => JFile}

import scala.annotation.tailrec


object Latex
{
  /** latex errors **/

  def latex_errors(dir: Path, root_name: String): List[String] =
  {
    val root_log_path = dir + Path.explode(root_name).ext("log")
    if (root_log_path.is_file) {
      for { (msg, pos) <- filter_errors(dir, File.read(root_log_path)) }
      yield "Latex error" + Position.here(pos) + ":\n" + cat_lines(split_lines(msg).map("  " + _))
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
            (0 /: source_lines.iterator.takeWhile({ case (m, _) => m <= l }))(
              { case (_, (_, n)) => n })
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
      val Pattern = """^(.*?\.\w\w\w):(\d+): (.*)$""".r
      def unapply(line: String): Option[(Path, Int, String)] =
        line match {
          case Pattern(file, Value.Int(line), message) =>
            val path = File.standard_path(file)
            if (Path.is_wellformed(path)) {
              val file = (dir + Path.explode(path)).canonical
              if (file.is_file) Some((file, line, message)) else None
            }
            else None
          case _ => None
        }
    }

    object Line_Error
    {
      val Pattern = """^l\.(\d+) (.*)$""".r
      def unapply(line: String): Option[(Int, String)] =
        line match {
          case Pattern(Value.Int(line), message) => Some((line, message))
          case _ => None
        }
    }

    @tailrec def filter(lines: List[String], result: List[(String, Position.T)])
      : List[(String, Position.T)] =
    {
      lines match {
        case File_Line_Error((file, line, msg1)) :: rest1 =>
          val pos = tex_file_position(file, line)
          rest1 match {
            case Line_Error((line2, msg2)) :: rest2 if line == line2 =>
              filter(rest2, (Exn.cat_message(msg1, msg2), pos) :: result)
            case _ =>
              filter(rest1, (msg1, pos) :: result)
          }
        case _ :: rest => filter(rest, result)
        case Nil => result.reverse
      }
    }

    filter(Line.logical_lines(root_log), Nil)
  }
}
