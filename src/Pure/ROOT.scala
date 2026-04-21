/*  Title:      Pure/ROOT.scala
    Author:     Makarius
    UUID:       b60ea865-fe16-4a2d-9764-1037e41f8964

Root of isabelle package.
*/

import java.io.{File => JFile}
import java.nio.file.{Path => JPath}

import scala.util.matching.Regex


package object isabelle {
  val ERROR = Exn.ERROR
  val error = Exn.error _
  def cat_error(msgs: String*): Nothing = Exn.cat_error(msgs:_*)

  def using[A <: AutoCloseable, B](x: A | Null)(f: A => B): B =
    Library.using(x)(f)
  def using_option[A <: AutoCloseable, B](opt: Option[A])(f: A => B): Option[B] =
    Library.using_option(opt)(f)
  def using_optional[A <: AutoCloseable, B](opt: Option[A])(f: Option[A] => B): B =
    Library.using_optional(opt)(f)

  val space_explode = Library.space_explode _
  val split_lines = Library.split_lines _
  val cat_lines = Library.cat_lines _
  val terminate_lines = Library.terminate_lines _
  val quote = Library.quote _
  val commas = Library.commas _
  val commas_quote = Library.commas_quote _
  def proper_value[A](x: A | Null): Option[A] = Library.proper_value(x)
  val proper_bool = Library.proper_bool _
  val proper_string = Library.proper_string _
  def proper_list[A](list: List[A] | Null): Option[List[A]] = Library.proper_list(list)
  def if_proper[A](x: Iterable[A] | Null, body: => String): String = Library.if_proper(x, body)
  def if_proper(b: Boolean, body: => String): String = Library.if_proper(b, body)

  extension (str: String) {
    def replacing(args: ((String | Regex), String)*): String =
      Library.replacing(str, args:_*)
  }

  extension (file: JFile) {
    def file_name: String = file.getName.nn
    def java_path: JPath = file.toPath.nn
  }

  extension (path: JPath) {
    def java_file: JFile = path.toFile.nn
  }

  extension (obj: AnyRef) {
    def class_name: String = obj.getClass.nn.getName.nn
  }
}
