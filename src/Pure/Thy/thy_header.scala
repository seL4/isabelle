/*  Title:      Pure/Thy/thy_header.scala
    ID:         $Id$
    Author:     Makarius

Theory header keywords.
*/

package isabelle

object ThyHeader {

  val HEADER = "header"
  val THEORY = "theory"
  val IMPORTS = "imports"
  val USES = "uses"
  val BEGIN = "begin"

  val keywords = List("%", "(", ")", ";", BEGIN, HEADER, IMPORTS, THEORY, USES)
}
