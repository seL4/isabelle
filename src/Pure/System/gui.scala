/*  Title:      Pure/System/gui.scala
    Author:     Makarius

Elementary GUI tools.
*/

package isabelle


import java.awt.{Image, Component, Toolkit}
import javax.swing.{ImageIcon, JOptionPane, UIManager}

import scala.swing.{ComboBox, TextArea, ScrollPane}
import scala.swing.event.SelectionChanged


object GUI
{
  /* Swing look-and-feel */

  def get_laf(): String =
  {
    def laf(name: String): Option[String] =
      UIManager.getInstalledLookAndFeels().find(_.getName == name).map(_.getClassName)

    if (Platform.is_windows || Platform.is_macos)
      UIManager.getSystemLookAndFeelClassName()
    else
      laf("Nimbus") orElse laf("GTK+") getOrElse
        UIManager.getCrossPlatformLookAndFeelClassName()
  }

  def init_laf(): Unit = UIManager.setLookAndFeel(get_laf())


  /* simple dialogs */

  def scrollable_text(txt: String, width: Int = 60, editable: Boolean = false): ScrollPane =
  {
    val text = new TextArea(txt)
    if (width > 0) text.columns = width
    text.editable = editable
    new ScrollPane(text)
  }

  private def simple_dialog(kind: Int, default_title: String,
    parent: Component, title: String, message: Seq[Any])
  {
    Swing_Thread.now {
      val java_message = message map { case x: scala.swing.Component => x.peer case x => x }
      JOptionPane.showMessageDialog(parent,
        java_message.toArray.asInstanceOf[Array[AnyRef]],
        if (title == null) default_title else title, kind)
    }
  }

  def dialog(parent: Component, title: String, message: Any*) =
    simple_dialog(JOptionPane.PLAIN_MESSAGE, null, parent, title, message)

  def warning_dialog(parent: Component, title: String, message: Any*) =
    simple_dialog(JOptionPane.WARNING_MESSAGE, "Warning", parent, title, message)

  def error_dialog(parent: Component, title: String, message: Any*) =
    simple_dialog(JOptionPane.ERROR_MESSAGE, "Error", parent, title, message)

  def confirm_dialog(parent: Component, title: String, option_type: Int, message: Any*): Int =
    Swing_Thread.now {
      val java_message = message map { case x: scala.swing.Component => x.peer case x => x }
      JOptionPane.showConfirmDialog(parent,
        java_message.toArray.asInstanceOf[Array[AnyRef]], title,
          option_type, JOptionPane.QUESTION_MESSAGE)
    }


  /* zoom box */

  class Zoom_Box(apply_factor: Int => Unit) extends ComboBox[String](
    List("50%", "70%", "85%", "100%", "125%", "150%", "175%", "200%", "300%", "400%"))
  {
    val Factor = "([0-9]+)%?".r
    def parse(text: String): Int =
      text match {
        case Factor(s) =>
          val i = Integer.parseInt(s)
          if (10 <= i && i <= 1000) i else 100
        case _ => 100
      }

    def print(i: Int): String = i.toString + "%"

    def set_item(i: Int) {
      peer.getEditor match {
        case null =>
        case editor => editor.setItem(print(i))
      }
    }

    makeEditable()(c => new ComboBox.BuiltInEditor(c)(text => print(parse(text)), x => x))
    reactions += {
      case SelectionChanged(_) => apply_factor(parse(selection.item))
    }
    listenTo(selection)
    selection.index = 3
    prototypeDisplayValue = Some("00000%")
  }


  /* screen resolution */

  def resolution_scale(): Double = Toolkit.getDefaultToolkit.getScreenResolution.toDouble / 72
  def resolution_scale(i: Int): Int = (i.toDouble * resolution_scale()).round.toInt


  /* icon */

  def isabelle_icon(): ImageIcon =
    new ImageIcon(getClass.getClassLoader.getResource("isabelle/isabelle.gif"))

  def isabelle_image(): Image = isabelle_icon().getImage
}

