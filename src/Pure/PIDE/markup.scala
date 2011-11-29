/*  Title:      Pure/PIDE/markup.scala
    Module:     PIDE
    Author:     Makarius

Generic markup elements.
*/

package isabelle


object Markup
{
  /* properties */

  val NAME = "name"
  val Name = new Properties.String(NAME)

  val KIND = "kind"
  val Kind = new Properties.String(KIND)


  /* elements */

  val Empty = Markup("", Nil)
  val Data = Markup("data", Nil)
  val Broken = Markup("broken", Nil)
}


sealed case class Markup(name: String, properties: Properties.T)

