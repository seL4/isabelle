/*  Title:      Pure/Tools/isabelle_syntax.scala
    ID:         $Id$
    Author:     Makarius

Isabelle outer syntax.
*/

package isabelle

import java.util.{Properties, Enumeration}


object IsabelleSyntax {

  /* string token */

  def append_string(str: String, result: StringBuilder) = {
    result.append("\"")
    for (c <- str) {
      if (c < 32 || c == '\\' || c == '\"') {
        result.append("\\")
        if (c < 10) result.append('0')
        if (c < 100) result.append('0')
        result.append(c.asInstanceOf[Int].toString)
      }
      else result.append(c)
    }
    result.append("\"")
  }

  def encode_string(str: String) = {
    val result = new StringBuilder(str.length + 20)
    append_string(str, result)
    result.toString
  }


  /* properties */

  def append_properties(props: Properties, result: StringBuilder) = {
    result.append("(")
    val names = props.propertyNames.asInstanceOf[Enumeration[String]]
    while (names.hasMoreElements) {
      val name = names.nextElement; val value = props.getProperty(name)
      append_string(name, result); result.append(" = "); append_string(value, result)
      if (names.hasMoreElements) result.append(", ")
    }
    result.append(")")
  }

  def encode_properties(props: Properties) = {
    val result = new StringBuilder(40)
    append_properties(props, result)
    result.toString
  }

}
