/*  Title:      Pure/ROOT.scala
    Author:     Makarius

Root of isabelle package.
*/

package object isabelle
{
  val ERROR = Exn.ERROR
  val error = Exn.error _
  def cat_error(msgs: String*): Nothing = Exn.cat_error(msgs:_*)

  def using[A <: AutoCloseable, B](a: A)(f: A => B): B = Library.using(a)(f)
  val space_explode = Library.space_explode _
  val split_lines = Library.split_lines _
  val cat_lines = Library.cat_lines _
  val terminate_lines = Library.terminate_lines _
  val quote = Library.quote _
  val commas = Library.commas _
  val commas_quote = Library.commas_quote _
  val proper_string = Library.proper_string _
  def proper_list[A](list: List[A]): Option[List[A]] = Library.proper_list(list)
}
