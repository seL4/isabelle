/*  Title:      Tools/jEdit/src/jedit_property.scala
    Author:     Makarius

Systematic access to jEdit properties.
*/

package isabelle.jedit


import isabelle._

import scala.collection.mutable
import org.gjt.sp.jedit.jEdit


object JEdit_Property {
  def init(name: String, value: String = ""): JEdit_Property =
    new JEdit_Property(name, value)

  def load(name: String, default: String = ""): JEdit_Property =
    new JEdit_Property(name, jEdit.getProperty(name, default))

  val menu_bar: JEdit_Property = init("view.mbar")
  val file_menu: JEdit_Property = init("file")
  val help_menu: JEdit_Property = init("help-menu")
}

final class JEdit_Property private(val name: String, val value: String) {
  override def toString: String = Properties.Eq(name, value)

  def load(): JEdit_Property = JEdit_Property.load(name)
  def save(): JEdit_Property = { jEdit.setProperty(name, value); this }

  def remove(args: String*): JEdit_Property = {
    val words1 = Word.explode(value)
    val words2 = args.foldLeft(words1) { case (ws, a) => Library.remove(a)(ws) }
    if (words1 == words2) this else new JEdit_Property(name, Word.implode(words2))
  }

  def insert_after(hook: String, args: String*): JEdit_Property = {
    val that = remove(args:_*)

    val words1 = Word.explode(that.value)
    val result = new mutable.ListBuffer[String]
    for (w <- words1) {
      result += w
      if (w == hook) {
        for (a <- args) result += a
      }
    }
    val words2 = result.toList

    if (words1 == words2) that else new JEdit_Property(name, Word.implode(words2))
  }
}
