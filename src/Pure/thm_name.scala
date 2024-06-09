/*  Title:      Pure/thm_name.scala
    Author:     Makarius

Systematic naming of individual theorems, as selections from multi-facts.
*/

package isabelle


import scala.math.Ordering


object Thm_Name {
  object Ordering extends scala.math.Ordering[Thm_Name] {
    def compare(thm_name1: Thm_Name, thm_name2: Thm_Name): Int =
      thm_name1.name compare thm_name2.name match {
        case 0 => thm_name1.index compare thm_name2.index
        case ord => ord
      }
  }

  def graph[A]: Graph[Thm_Name, A] = Graph.empty(Ordering)

  private val Thm_Name_Regex = """^(.)+\((\d+)\)$""".r

  val empty: Thm_Name = Thm_Name("", 0)

  def parse(s: String): Thm_Name =
    s match {
      case Thm_Name_Regex(name, Value.Nat(index)) => Thm_Name(name, index)
      case _ => Thm_Name(s, 0)
    }


  /* XML data representation */

  def encode: XML.Encode.T[Thm_Name] = { (thm_name: Thm_Name) =>
    import XML.Encode._
    pair(string, int)((thm_name.name, thm_name.index))
  }

  def decode: XML.Decode.T[Thm_Name] = { (body: XML.Body) =>
    import XML.Decode._
    val (name, index) = pair(string, int)(body)
    Thm_Name(name, index)
  }
}

sealed case class Thm_Name(name: String, index: Int) {
  def is_empty: Boolean = name.isEmpty

  def print: String =
    if (name == "" || index == 0) name
    else name + "(" + index + ")"

  def short: String =
    if (name == "" || index == 0) name
    else name + "_" + index
}
