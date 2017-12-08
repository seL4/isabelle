/*  Title:      Pure/Thy/latex.scala
    Author:     Makarius

Support for LaTeX.
*/

package isabelle


import scala.annotation.tailrec


object Latex
{
  sealed case class Error(file: Option[Path], line: Int, message: String)

  def filter_errors(dir: Path, text: String): List[Error] =
  {
    object File_Line_Error
    {
      val Pattern = """^(.*):(\d+): (.*)$""".r
      def unapply(line: String): Option[Error] =
        line match {
          case Pattern(file, Value.Int(line), message) =>
            val path = File.standard_path(file)
            if (Path.is_wellformed(path)) {
              val file = Path.explode(path)
              if ((dir + file).is_file) Some(Error(Some(file), line, message)) else None
            }
            else None
          case _ => None
        }
    }

    object Line_Error
    {
      val Pattern = """^l\.(\d+) (.*)$""".r
      def unapply(line: String): Option[Error] =
        line match {
          case Pattern(Value.Int(line), message) => Some(Error(None, line, message))
          case _ => None
        }
    }

    @tailrec def filter(lines: List[String], result: List[Error]): List[Error] =
      lines match {
        case File_Line_Error(err1) :: rest1 =>
          rest1 match {
            case Line_Error(err2) :: rest2 if err1.line == err2.line =>
              val err = err1.copy(message = Exn.cat_message(err1.message, err2.message))
              filter(rest2, err :: result)
            case _ => filter(rest1, err1 :: result)
          }
        case _ :: rest => filter(rest, result)
        case Nil => result.reverse
      }

    filter(split_lines(text), Nil)
  }
}
