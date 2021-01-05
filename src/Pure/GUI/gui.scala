/*  Title:      Pure/GUI/gui.scala
    Author:     Makarius

Basic GUI tools (for AWT/Swing).
*/

package isabelle

import java.awt.{Component, Container, Font, Image, Insets, KeyboardFocusManager, Window, Point,
  Rectangle, Dimension, GraphicsEnvironment, MouseInfo, Toolkit}
import java.awt.font.{FontRenderContext, LineMetrics, TextAttribute, TransformAttribute}
import java.awt.geom.AffineTransform
import javax.swing.{ImageIcon, JButton, JDialog, JFrame, JLabel, JLayeredPane, JOptionPane,
  JTextField, JWindow, LookAndFeel, UIManager, SwingUtilities}
import scala.swing.{ComboBox, ScrollPane, TextArea}
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

  def current_laf(): String = UIManager.getLookAndFeel.getClass.getName()

  def is_macos_laf(): Boolean =
    Platform.is_macos && UIManager.getSystemLookAndFeelClassName() == current_laf()

  def is_windows_laf(): Boolean =
    Platform.is_windows && UIManager.getSystemLookAndFeelClassName() == current_laf()


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

  def isabelle_image_large(): Image =
    Toolkit.getDefaultToolkit.getImage(
      File.platform_path(Path.explode("~~/lib/logo/isabelle_transparent-128.png")))

  def set_application_icon()
  {
    if (Platform.is_macos) {
      val image = isabelle_image_large()
      val app =
        Class.forName("com.apple.eawt.Application")
          .getDeclaredMethod("getApplication").invoke(null)
      app.getClass.getDeclaredMethod("setDockIconImage", classOf[Image]).invoke(app, image)
    }
  }


  /* location within multi-screen environment */

  final case class Screen_Location(point: Point, bounds: Rectangle)
  {
    def relative(parent: Component, size: Dimension): Point =
    {
      val w = size.width
      val h = size.height

      val x0 = parent.getLocationOnScreen.x
      val y0 = parent.getLocationOnScreen.y
      val x1 = x0 + parent.getWidth - w
      val y1 = y0 + parent.getHeight - h
      val x2 = point.x min (bounds.x + bounds.width - w)
      val y2 = point.y min (bounds.y + bounds.height - h)

      val location = new Point((x2 min x1) max x0, (y2 min y1) max y0)
      SwingUtilities.convertPointFromScreen(location, parent)
      location
    }
  }

  def screen_location(component: Component, point: Point): Screen_Location =
  {
    val screen_point = new Point(point.x, point.y)
    if (component != null) SwingUtilities.convertPointToScreen(screen_point, component)

    val ge = GraphicsEnvironment.getLocalGraphicsEnvironment
    val screen_bounds =
      (for {
        device <- ge.getScreenDevices.iterator
        config <- device.getConfigurations.iterator
        bounds = config.getBounds
      } yield bounds).find(_.contains(screen_point)) getOrElse ge.getMaximumWindowBounds

    Screen_Location(screen_point, screen_bounds)
  }

  def mouse_location(): Screen_Location =
    screen_location(null, MouseInfo.getPointerInfo.getLocation)


  /* screen size */

  sealed case class Screen_Size(bounds: Rectangle, insets: Insets)
  {
    def full_screen_bounds: Rectangle =
      if (Platform.is_linux) {
        // avoid menu bar and docking areas
        new Rectangle(
          bounds.x + insets.left,
          bounds.y + insets.top,
          bounds.width - insets.left - insets.right,
          bounds.height - insets.top - insets.bottom)
      }
      else if (Platform.is_macos) {
        // avoid menu bar, but ignore docking areas
        new Rectangle(
          bounds.x,
          bounds.y + insets.top,
          bounds.width,
          bounds.height - insets.top)
      }
      else bounds
  }

  def screen_size(component: Component): Screen_Size =
  {
    val config = component.getGraphicsConfiguration
    val bounds = config.getBounds
    val insets = Toolkit.getDefaultToolkit.getScreenInsets(config)
    Screen_Size(bounds, insets)
  }


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
