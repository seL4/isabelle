/*  Title:      Tools/jEdit/src/jedit_font.scala
    Author:     Makarius

Font information, derived from main view font.
*/

package isabelle.jedit


import isabelle._


import java.awt.Font

import org.gjt.sp.jedit.{jEdit, View}


object Font_Info
{
  val dummy: Font_Info = Font_Info("Dialog", 12.0f)


  /* size range */

  val min_size = 5
  val max_size = 250

  def restrict_size(size: Float): Float = size max min_size min max_size


  /* jEdit font */

  def main_family(): String = jEdit.getProperty("view.font")

  def main_size(scale: Double = 1.0): Float =
    restrict_size(jEdit.getIntegerProperty("view.fontsize", 16).toFloat * scale.toFloat)

  def main(scale: Double = 1.0): Font_Info =
    Font_Info(main_family(), main_size(scale))

  def main_change(change: Float => Float)
  {
    val size0 = main_size()
    val size = restrict_size(change(size0)).round
    if (size != size0) {
      jEdit.setIntegerProperty("view.fontsize", size)
      jEdit.propertiesChanged()
      jEdit.saveSettings()
      jEdit.getActiveView().getStatus.setMessageAndClear("Text font size: " + size)
    }
  }
}

sealed case class Font_Info(family: String, size: Float)
{
  def font: Font = new Font(family, Font.PLAIN, size.round)
}

