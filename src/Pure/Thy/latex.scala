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

  private val File_Pattern = """^.*%:%file=(.+)%:%$""".r
  private val Range_Pattern2 = """^.*%:%range=(\d+):(\d+)%:%$""".r
  private val Range_Pattern1 = """^.*%:%range=(\d+)%:%$""".r

  def read_tex_file(tex_file: Path): Tex_File =
    new Tex_File(tex_file, Line.logical_lines(File.read(tex_file)).toArray)

  final class Tex_File private[Latex](val tex_file: Path, tex_lines: Array[String])
  {
    override def toString: String = tex_file.toString

    val source_file: Option[Path] =
      if (tex_lines.length > 0) {
        tex_lines(0) match {
          case File_Pattern(file) if Path.is_wellformed(file) && Path.explode(file).is_file =>
            Some(Path.explode(file))
          case _ => None
        }
      }
      else None

    val source_content: Line.Document =
      source_file match {
        case Some(file) => Line.Document(Symbol.decode(File.read(file)))
        case None => Line.Document.empty
      }

    lazy val source_chunk: Symbol.Text_Chunk =
      Symbol.Text_Chunk(source_content.text)

    def source_position(l: Int): Option[Position.T] =
      for {
        file <- source_file
        if 0 < l && l <= tex_lines.length
        line = tex_lines(l - 1)
        if line.endsWith("%:%")
        symbol_range <-
          (line match {
            case Range_Pattern2(Value.Int(i), Value.Int(j)) => Some(Text.Range(i, j))
            case Range_Pattern1(Value.Int(i)) => Some(Text.Range(i, i + 1))
            case _ => None
          })
        range <- source_chunk.incorporate(symbol_range)
      }
      yield {
        Position.Line_File(source_content.position(range.start).line1, file.implode) :::
        Position.Range(symbol_range)
      }

    def tex_position(line: Int): Position.T =
        Position.Line_File(line, tex_file.implode)

    def position(line: Int): Position.T =
      source_position(line) getOrElse tex_position(line)
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
      val Pattern = """^(.*):(\d+): (.*)$""".r
      def unapply(line: String): Option[(Path, Int, String)] =
        line match {
          case Pattern(file, Value.Int(line), message) =>
            val path = File.standard_path(file)
            if (Path.is_wellformed(path)) {
              val file = dir + Path.explode(path)
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
          val pos = tex_file_position((dir + file).canonical, line)
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
