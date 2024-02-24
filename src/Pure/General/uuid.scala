/*  Title:      Pure/General/uuid.scala
    Author:     Makarius

Universally Unique Identifiers.
*/

package isabelle


object UUID {
  type T = java.util.UUID

  def random(): T = java.util.UUID.randomUUID()
  def random_string(): String = random().toString

  def unapply(s: String): Option[T] =
    try { Some(java.util.UUID.fromString(s)) }
    catch { case _: IllegalArgumentException => None }

  def unapply(body: XML.Body): Option[T] = unapply(XML.content(body))

  def make(s: String): T =
    unapply(s).getOrElse(error("Bad UUID: " + quote(s)))
}
