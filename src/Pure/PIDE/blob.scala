/*  Title:      Pure/PIDE/blob.scala
    Author:     Makarius

Unidentified text with markup.
*/

package isabelle


object Blob
{
  sealed case class State(val blob: Blob, val markup: Markup_Tree = Markup_Tree.empty)
  {
    def + (info: Text.Markup): State = copy(markup = markup + info)
  }
}


sealed case class Blob(val source: String)
{
  def source(range: Text.Range): String = source.substring(range.start, range.stop)

  lazy val symbol_index = new Symbol.Index(source)
  def decode(i: Text.Offset): Text.Offset = symbol_index.decode(i)
  def decode(r: Text.Range): Text.Range = symbol_index.decode(r)

  val empty_state: Blob.State = Blob.State(this)
}
