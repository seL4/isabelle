/*  Title:      Tools/Graphview/src/parameters.scala
    Author:     Markus Kaiser, TU Muenchen

Visual parameters.
*/

package isabelle.graphview

import isabelle._

import java.awt.Color


class Parameters
{
  val font_family: String = "IsabelleText"
  val font_size: Int = 14
  val gap_x = 20
  val pad_x = 8
  val pad_y = 5

  val tooltip_font_size: Int = 10

  var arrow_heads = false

  object Colors
  {
    private val Filter_Colors = List(
      new Color(0xD9, 0xF2, 0xE2), //blue
      new Color(0xFF, 0xE7, 0xD8), //orange
      new Color(0xFF, 0xFF, 0xE5), //yellow
      new Color(0xDE, 0xCE, 0xFF), //lilac
      new Color(0xCC, 0xEB, 0xFF), //turquoise
      new Color(0xFF, 0xE5, 0xE5), //red
      new Color(0xE5, 0xE5, 0xD9)  //green
    )

    private var curr : Int = -1
    def next(): Color =
    {
      curr = (curr + 1) % Filter_Colors.length
      Filter_Colors(curr)
    }
  }
}
