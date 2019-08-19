/*  Title:      Pure/thm_name.scala
    Author:     Makarius

Systematic naming of individual theorems, as selections from multi-facts.
*/

package isabelle


import scala.math.Ordering


object Thm_Name
{
  object Ordering extends scala.math.Ordering[Thm_Name]
  {
    def compare(thm_name1: Thm_Name, thm_name2: Thm_Name): Int =
      thm_name1.name compare thm_name2.name match {
        case 0 => thm_name1.index compare thm_name2.index
        case ord => ord
      }
  }

  def graph[A]: Graph[Thm_Name, A] = Graph.empty(Ordering)
}

sealed case class Thm_Name(name: String, index: Int)
{
  override def toString: String =
    if (name == "" || index == 0) name
    else name + "(" + index + ")"

  def flatten: String =
    if (name == "" || index == 0) name
    else name + "_" + index
}
