/*  Title:      Pure/GUI/gui.scala
    Author:     Makarius

Basic GUI tools (for AWT/Swing).
*/

package isabelle

import java.lang.{ClassLoader, ClassNotFoundException, NoSuchMethodException}
import java.awt.{Image, Component, Container, Toolkit, Window, Font, KeyboardFocusManager}
import java.awt.font.{TextAttribute, TransformAttribute, FontRenderContext, LineMetrics}
import java.awt.geom.AffineTransform
import javax.swing.{ImageIcon, JOptionPane, UIManager, JLayeredPane, JFrame, JWindow, JDialog,
  JButton, JTextField, JLabel}


import scala.collection.JavaConverters
import scala.swing.{ComboBox, TextArea, ScrollPane}
import scala.swing.event.SelectionChanged


object GUI
{
  /* Swing look-and-feel */

  def find_laf(name: String): Option[String] =
    UIManager.getInstalledLookAndFeels().
      find(c => c.getName == name || c.getClassName == name).
      map(_.getClassName)

  def get_laf(): String =
    find_laf(System.getProperty("isabelle.laf")) getOrElse {
      if (Platform.is_windows || Platform.is_macos)
        UIManager.getSystemLookAndFeelClassName()
      else
        UIManager.getCrossPlatformLookAndFeelClassName()
    }

  def init_laf(): Unit = UIManager.setLookAndFeel(get_laf())

  def is_macos_laf(): Boolean =
    Platform.is_macos &&
    UIManager.getSystemLookAndFeelClassName() == UIManager.getLookAndFeel.getClass.getName

  def is_windows_laf(): Boolean =
    Platform.is_windows &&
    UIManager.getSystemLookAndFeelClassName() == UIManager.getLookAndFeel.getClass.getName


  /* plain focus traversal, notably for text fields */

  def plain_focus_traversal(component: Component)
  {
    val dummy_button = new JButton
    def apply(id: Int): Unit =
      component.setFocusTraversalKeys(id, dummy_button.getFocusTraversalKeys(id))
    apply(KeyboardFocusManager.FORWARD_TRAVERSAL_KEYS)
    apply(KeyboardFocusManager.BACKWARD_TRAVERSAL_KEYS)
  }


  /* simple dialogs */

  def scrollable_text(raw_txt: String, width: Int = 60, height: Int = 20, editable: Boolean = false)
    : ScrollPane =
  {
    val txt = Output.clean_yxml(raw_txt)
    val text = new TextArea(txt)
    if (width > 0) text.columns = width
    if (height > 0 && split_lines(txt).length > height) text.rows = height
    text.editable = editable
    new ScrollPane(text)
  }

  private def simple_dialog(kind: Int, default_title: String,
    parent: Component, title: String, message: Iterable[Any])
  {
    GUI_Thread.now {
      val java_message =
        message.iterator.map({ case x: scala.swing.Component => x.peer case x => x }).
          toArray.asInstanceOf[Array[AnyRef]]
      JOptionPane.showMessageDialog(parent, java_message,
        if (title == null) default_title else title, kind)
    }
  }

  def dialog(parent: Component, title: String, message: Any*): Unit =
    simple_dialog(JOptionPane.PLAIN_MESSAGE, null, parent, title, message)

  def warning_dialog(parent: Component, title: String, message: Any*): Unit =
    simple_dialog(JOptionPane.WARNING_MESSAGE, "Warning", parent, title, message)

  def error_dialog(parent: Component, title: String, message: Any*): Unit =
    simple_dialog(JOptionPane.ERROR_MESSAGE, "Error", parent, title, message)

  def confirm_dialog(parent: Component, title: String, option_type: Int, message: Any*): Int =
    GUI_Thread.now {
      val java_message = message map { case x: scala.swing.Component => x.peer case x => x }
      JOptionPane.showConfirmDialog(parent,
        java_message.toArray.asInstanceOf[Array[AnyRef]], title,
          option_type, JOptionPane.QUESTION_MESSAGE)
    }


  /* zoom box */

  private val Zoom_Factor = "([0-9]+)%?".r

  abstract class Zoom_Box extends ComboBox[String](
    List("50%", "70%", "85%", "100%", "125%", "150%", "175%", "200%", "300%", "400%"))
  {
    def changed: Unit
    def factor: Int = parse(selection.item)

    private def parse(text: String): Int =
      text match {
        case Zoom_Factor(s) =>
          val i = Integer.parseInt(s)
          if (10 <= i && i < 1000) i else 100
        case _ => 100
      }

    private def print(i: Int): String = i.toString + "%"

    def set_item(i: Int) {
      peer.getEditor match {
        case null =>
        case editor => editor.setItem(print(i))
      }
    }

    makeEditable()(c => new ComboBox.BuiltInEditor(c)(text => print(parse(text)), x => x))
    peer.getEditor.getEditorComponent match {
      case text: JTextField => text.setColumns(4)
      case _ =>
    }

    selection.index = 3

    listenTo(selection)
    reactions += { case SelectionChanged(_) => changed }
  }


  /* tooltip with multi-line support */

  def tooltip_lines(text: String): String =
    if (text == null || text == "") null
    else "<html>" + HTML.output(text) + "</html>"


  /* icon */

  def isabelle_icon(): ImageIcon =
    new ImageIcon(getClass.getClassLoader.getResource("isabelle/isabelle_transparent-32.gif"))

  def isabelle_icons(): List[ImageIcon] =
    for (icon <- List("isabelle/isabelle_transparent-32.gif", "isabelle/isabelle_transparent.gif"))
      yield new ImageIcon(getClass.getClassLoader.getResource(icon))

  def isabelle_image(): Image = isabelle_icon().getImage


  /* component hierachy */

  def get_parent(component: Component): Option[Container] =
    component.getParent match {
      case null => None
      case parent => Some(parent)
    }

  def ancestors(component: Component): Iterator[Container] = new Iterator[Container] {
    private var next_elem = get_parent(component)
    def hasNext(): Boolean = next_elem.isDefined
    def next(): Container =
      next_elem match {
        case Some(parent) =>
          next_elem = get_parent(parent)
          parent
        case None => Iterator.empty.next()
      }
  }

  def parent_window(component: Component): Option[Window] =
    ancestors(component).collectFirst({ case x: Window => x })

  def layered_pane(component: Component): Option[JLayeredPane] =
    parent_window(component) match {
      case Some(w: JWindow) => Some(w.getLayeredPane)
      case Some(w: JFrame) => Some(w.getLayeredPane)
      case Some(w: JDialog) => Some(w.getLayeredPane)
      case _ => None
    }

  def traverse_components(component: Component, apply: Component => Unit)
  {
    def traverse(comp: Component)
    {
      apply(comp)
      comp match {
        case cont: Container =>
          for (i <- 0 until cont.getComponentCount)
            traverse(cont.getComponent(i))
        case _ =>
      }
    }
    traverse(component)
  }


  /* font operations */

  def copy_font(font: Font): Font =
    if (font == null) null
    else new Font(font.getFamily, font.getStyle, font.getSize)

  def line_metrics(font: Font): LineMetrics =
    font.getLineMetrics("", new FontRenderContext(null, false, false))

  def transform_font(font: Font, transform: AffineTransform): Font =
    font.deriveFont(java.util.Map.of(TextAttribute.TRANSFORM, new TransformAttribute(transform)))

  def font(family: String = Isabelle_Fonts.sans, size: Int = 1, bold: Boolean = false): Font =
    new Font(family, if (bold) Font.BOLD else Font.PLAIN, size)

  def label_font(): Font = (new JLabel).getFont


  /* Isabelle fonts */

  def imitate_font(font: Font,
    family: String = Isabelle_Fonts.sans,
    scale: Double = 1.0): Font =
  {
    val font1 = new Font(family, font.getStyle, font.getSize)
    val rel_size = line_metrics(font).getHeight.toDouble / line_metrics(font1).getHeight
    new Font(family, font.getStyle, (scale * rel_size * font.getSize).toInt)
  }

  def imitate_font_css(font: Font,
    family: String = Isabelle_Fonts.sans,
    scale: Double = 1.0): String =
  {
    val font1 = new Font(family, font.getStyle, font.getSize)
    val rel_size = line_metrics(font).getHeight.toDouble / line_metrics(font1).getHeight
    "font-family: " + family + "; font-size: " + (scale * rel_size * 100).toInt + "%;"
  }

  def use_isabelle_fonts()
  {
    val default_font = label_font()
    val ui = UIManager.getDefaults
    for (prop <- List(
      "ToggleButton.font",
      "CheckBoxMenuItem.font",
      "Label.font",
      "Menu.font",
      "MenuItem.font",
      "PopupMenu.font",
      "Table.font",
      "TableHeader.font",
      "TextArea.font",
      "TextField.font",
      "TextPane.font",
      "ToolTip.font",
      "Tree.font"))
    {
      val font = ui.get(prop) match { case font: Font => font case _ => default_font }
      ui.put(prop, GUI.imitate_font(font))
    }
  }
}
