/*  Title:      Tools/Graphview/src/parameters.scala
    Author:     Markus Kaiser, TU Muenchen

Visual parameters with fallbacks for non-jEdit-environment.
*/

package isabelle.graphview

import isabelle._

import java.awt.Color


object Parameters
{
  val font_family: String = "IsabelleText"
  val font_size: Int = 16

  //Should not fail since this is in the isabelle environment.
  def tooltip_css(): String =
    File.try_read(
      Path.split(Isabelle_System.getenv_strict("JEDIT_STYLE_SHEETS")))
  
  object Colors {
    val Filter_Colors = List(
      
      new Color(0xD9, 0xF2, 0xE2), //blue
      new Color(0xFF, 0xE7, 0xD8), //orange
      new Color(0xFF, 0xFF, 0xE5), //yellow
      new Color(0xDE, 0xCE, 0xFF), //lilac
      new Color(0xCC, 0xEB, 0xFF), //turquoise
      new Color(0xFF, 0xE5, 0xE5), //red
      new Color(0xE5, 0xE5, 0xD9)  //green
    )

    private var curr : Int = -1
    def next = {
      this.synchronized {
        curr = (curr + 1) % Filter_Colors.length
        Filter_Colors(curr)
      }
    }
    
    val Default = Color.WHITE
    val No_Axioms = Color.LIGHT_GRAY
  }
  
  var long_names = true
  var arrow_heads = false
}
