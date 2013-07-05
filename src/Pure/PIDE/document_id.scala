/*  Title:      Pure/PIDE/document_id.scala
    Author:     Makarius

Unique identifiers for document structure.

NB: ML ticks forwards > 0, JVM ticks backwards < 0.
*/

package isabelle


object Document_ID
{
  type ID = Long
  val ID = Properties.Value.Long

  type Version = ID
  type Command = ID
  type Exec = ID

  val none: ID = 0
  val make = Counter()
}

