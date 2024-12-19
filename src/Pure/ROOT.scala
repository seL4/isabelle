/*  Title:      Pure/ROOT.scala
    Author:     Makarius
    UUID:       d4ac0ad0-9374-4722-b755-018dd6dd0e3b

Root of isabelle package.
*/

package object isabelle {
  val ERROR = Exn.ERROR
  val error = Exn.error _
  def cat_error(msgs: String*): Nothing = Exn.cat_error(msgs:_*)

  def using[A <: AutoCloseable, B](a: A)(f: A => B): B =
    Library.using(a)(f)
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
  val proper_bool = Library.proper_bool _
  val proper_string = Library.proper_string _
  def proper_list[A](list: List[A]): Option[List[A]] = Library.proper_list(list)
  def if_proper[A](x: Iterable[A], body: => String): String = Library.if_proper(x, body)
  def if_proper(b: Boolean, body: => String): String = Library.if_proper(b, body)
}
