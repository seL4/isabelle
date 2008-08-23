/*  Title:      Pure/General/markup.scala
    ID:         $Id$
    Author:     Makarius

Common markup elements.
*/

package isabelle

object Markup {

  /* position */

  val LINE = "line"
  val COLUMN = "column"
  val OFFSET = "offset"
  val END_LINE = "end_line"
  val END_COLUMN = "end_column"
  val END_OFFSET = "end_offset"
  val FILE = "file"
  val ID = "id"


  /* messages */

  val PID = "pid"
  val SESSION = "session"


  /* content */

  val ROOT = "root"
  val RAW = "raw"
  val BAD = "bad"
}
