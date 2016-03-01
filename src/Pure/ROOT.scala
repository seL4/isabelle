/*  Title:      Pure/ROOT.scala
    Module:     PIDE
    Author:     Makarius

Root of isabelle package.
*/

package object isabelle
{
  object Distribution     /*filled-in by makedist*/
  {
    val version = "unidentified repository version"
    val is_identified = false
    val is_official = false
  }

  val ERROR = Exn.ERROR
  val error = Exn.error _
  val cat_error = Exn.cat_error _

  val space_explode = Library.space_explode _
  val split_lines = Library.split_lines _
  val cat_lines = Library.cat_lines _
  val quote = Library.quote _
  val commas = Library.commas _
  val commas_quote = Library.commas_quote _
}
