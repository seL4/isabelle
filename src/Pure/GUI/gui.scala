/*  Title:      Pure/GUI/gui.scala
    Author:     Makarius

Basic GUI tools (for AWT/Swing).
*/

package isabelle

import java.util.{Map => JMap}
import java.awt.{Component, Container, Font, Image, Insets, KeyboardFocusManager, Window, Point,
  Rectangle, Dimension, GraphicsEnvironment, MouseInfo, Toolkit}
import java.awt.event.{KeyAdapter, KeyEvent, ItemListener, ItemEvent}
import java.awt.font.{FontRenderContext, LineMetrics, TextAttribute, TransformAttribute}
import java.awt.geom.AffineTransform
import javax.swing.{ImageIcon, JButton, JDialog, JFrame, JLabel, JLayeredPane, JOptionPane,
  RootPaneContainer, JTextField, JWindow, JComboBox, LookAndFeel, UIManager, SwingUtilities}

import scala.swing.{CheckBox, ComboBox, ScrollPane, TextArea, ListView, Label, Separator,
  Orientation}
import scala.swing.event.{ButtonClicked, SelectionChanged}


object GUI {
  /* Swing look-and-feel */

  def init_laf(): Unit = com.formdev.flatlaf.FlatLightLaf.setup()

  def current_laf(): String = UIManager.getLookAndFeel.getClass.getName()

  def is_macos_laf: Boolean =
    Platform.is_macos && UIManager.getSystemLookAndFeelClassName() == current_laf()

  class Look_And_Feel(laf: LookAndFeel) extends Isabelle_System.Service {
    def info: UIManager.LookAndFeelInfo =
      new UIManager.LookAndFeelInfo(laf.getName, laf.getClass.getName)
  }

  lazy val look_and_feels: List[Look_And_Feel] =
    Isabelle_System.make_services(classOf[Look_And_Feel])

  def init_lafs(): Unit = {
    val old_lafs =
      Set(
        "com.sun.java.swing.plaf.motif.MotifLookAndFeel",
        "com.sun.java.swing.plaf.windows.WindowsClassicLookAndFeel")
    val lafs =
      UIManager.getInstalledLookAndFeels().toList
        .filterNot(info => old_lafs(info.getClassName))
    val more_lafs = look_and_feels.map(_.info)
    UIManager.setInstalledLookAndFeels((more_lafs ::: lafs).toArray)

    // see https://www.formdev.com/flatlaf/customizing
    UIManager.put("Component.arrowType", "triangle")
  }


  /* additional look-and-feels */

  /* plain focus traversal, notably for text fields */

  def plain_focus_traversal(component: Component): Unit = {
    val dummy_button = new JButton
    def apply(id: Int): Unit =
      component.setFocusTraversalKeys(id, dummy_button.getFocusTraversalKeys(id))
    apply(KeyboardFocusManager.FORWARD_TRAVERSAL_KEYS)
    apply(KeyboardFocusManager.BACKWARD_TRAVERSAL_KEYS)
  }


  /* named items */

  enum Style { case plain, html, symbol_encoded, symbol_decoded }

  def make_bold(str: String, style: Style = Style.plain): String =
    style match {
      case Style.plain => str
      case Style.html => "<b>" + HTML.output(str) + "</b>"
      case _ =>
        val b = if (style == Style.symbol_encoded) Symbol.bold else Symbol.bold_decoded
        Symbol.iterator(str)
          .flatMap(s => if (Symbol.is_controllable(s)) List(b, s) else List(s))
          .mkString
    }

  sealed case class Name(
    name: String,
    kind: String = "",
    prefix: String = "",
    style: Style = Style.plain
  ) {
    override def toString: String = {
      val a = kind.nonEmpty
      val b = name.nonEmpty
      val k = if_proper(kind, make_bold(kind, style = style))
      prefix + if_proper(a || b,
        if_proper(prefix, ": ") + k + if_proper(a && b, " ") + if_proper(b, quote(name)))
    }
  }


  /* simple dialogs */

  def scrollable_text(
    raw_txt: String,
    width: Int = 60,
    height: Int = 20,
    editable: Boolean = false
  ) : ScrollPane = {
    val txt = Protocol_Message.clean_output(raw_txt)
    val text = new TextArea(txt)
    if (width > 0) text.columns = width
    if (height > 0 && split_lines(txt).length > height) text.rows = height
    text.editable = editable
    new ScrollPane(text)
  }

  private def simple_dialog(
    kind: Int,
    default_title: String,
    parent: Component,
    title: String,
    message: Iterable[Any]
  ): Unit = {
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


  /* basic GUI components */

  class Button(label: String) extends scala.swing.Button(label) {
    def clicked(): Unit = {}

    reactions += { case ButtonClicked(_) => clicked() }
  }

  class Check(label: String, init: Boolean = false) extends CheckBox(label) {
    def clicked(state: Boolean): Unit = {}
    def clicked(): Unit = {}

    selected = init
    reactions += { case ButtonClicked(_) => clicked(selected); clicked() }
  }


  /* list selector */

  object Selector {
    sealed abstract class Entry[A] { def get_value: Option[A] = Value.unapply(this) }
    object Value {
      def unapply[A](entry: Entry[A]): Option[A] =
        entry match {
          case item: Item[_] => Some(item.value)
          case _ => None
        }
    }
    def item[A](value: A): Entry[A] = Item(value, "", 0)
    def item_description[A](value: A, description: String): Entry[A] = Item(value, description, 0)

    private case class Item[A](value: A, description: String, batch: Int) extends Entry[A] {
      override def toString: String = proper_string(description) getOrElse value.toString
    }
    private case class Separator[A](batch: Int) extends Entry[A] {
      override def toString: String = "---"
    }

    private def make_entries[A](batches: List[List[Entry[A]]]): List[Entry[A]] = {
      val item_batches = batches.map(_.flatMap(Library.as_subclass(classOf[Item[A]])))
      val sep_entries: List[Entry[A]] =
        item_batches.filter(_.nonEmpty).zipWithIndex.flatMap({ case (batch, i) =>
          Separator[A](i) :: batch.map(_.copy(batch = i))
        })
      sep_entries.tail
    }
  }

  class Selector[A](batches: List[Selector.Entry[A]]*)
  extends ComboBox[Selector.Entry[A]](Selector.make_entries(batches.toList)) {
    def changed(): Unit = {}

    lazy val entries: List[Selector.Entry[A]] = Selector.make_entries(batches.toList)

    def find_value(pred: A => Boolean): Option[Selector.Entry[A]] =
      entries.find({ case item: Selector.Item[A] => pred(item.value) case _ => false })

    def selection_value: Option[A] = selection.item.get_value

    override lazy val peer: JComboBox[Selector.Entry[A]] =
      new JComboBox[Selector.Entry[A]](ComboBox.newConstantModel(entries)) with SuperMixin {
        private var key_released = false
        private var sep_selected = false

        addKeyListener(new KeyAdapter {
          override def keyPressed(e: KeyEvent): Unit = { key_released = false }
          override def keyReleased(e: KeyEvent): Unit = { key_released = true }
        })

        override def setSelectedIndex(i: Int): Unit = {
          getItemAt(i) match {
            case _: Selector.Separator[_] =>
              if (key_released) { sep_selected = true }
              else {
                val k = getSelectedIndex()
                val j = if (i > k) i + 1 else i - 1
                if (0 <= j && j < dataModel.getSize()) super.setSelectedIndex(j)
              }
            case _ => super.setSelectedIndex(i)
          }
        }

        override def setPopupVisible(visible: Boolean): Unit = {
          if (sep_selected) { sep_selected = false}
          else super.setPopupVisible(visible)
        }
      }

    private val default_renderer = renderer
    private val render_separator = new Separator
    renderer =
      (list: ListView[_ <: Selector.Entry[A]], selected: Boolean, focus: Boolean, entry: Selector.Entry[A], i: Int) => {
        entry match {
          case _: Selector.Separator[_] => render_separator
          case _ => default_renderer.componentFor(list, selected, focus, entry, i)
        }
      }

    listenTo(selection)
    reactions += { case SelectionChanged(_) => changed() }
  }


  /* zoom factor */

  private val Percent = "([0-9]+)%?".r

  class Zoom extends Selector[String](
    List("50%", "70%", "85%", "100%", "125%", "150%", "175%", "200%", "300%", "400%")
      .map(GUI.Selector.item)
  ) {
    def percent: Int = parse(selection.item.toString)
    def scale: Double = 0.01 * percent

    private def parse(text: String): Int =
      text match {
        case Percent(s) =>
          val i = Integer.parseInt(s)
          if (10 <= i && i < 1000) i else 100
        case _ => 100
      }

    private def print(i: Int): String = i.toString + "%"

    def set_item(i: Int): Unit = {
      peer.getEditor match {
        case null =>
        case editor => editor.setItem(print(i))
      }
    }

    makeEditable()(c =>
      new ComboBox.BuiltInEditor(c)(text => Selector.item(print(parse(text))), _.toString))
    peer.getEditor.getEditorComponent match {
      case text: JTextField => text.setColumns(4)
      case _ =>
    }

    selection.index = 3
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


  /* location within multi-screen environment */

  final case class Screen_Location(point: Point, bounds: Rectangle) {
    def relative(parent: Component, size: Dimension): Point = {
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

  def screen_location(component: Component, point: Point): Screen_Location = {
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

  sealed case class Screen_Size(bounds: Rectangle, insets: Insets) {
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

  def screen_size(component: Component): Screen_Size = {
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
    def hasNext: Boolean = next_elem.isDefined
    def next(): Container =
      next_elem match {
        case Some(parent) =>
          next_elem = get_parent(parent)
          parent
        case None => Iterator.empty.next()
      }
  }

  def parent_window(component: Component): Option[Window] =
    ancestors(component).collectFirst({ case c: Window => c })

  def layered_pane(component: Component): Option[JLayeredPane] =
    parent_window(component) match {
      case Some(c: RootPaneContainer) => Some(c.getLayeredPane)
      case _ => None
    }

  def traverse_components(component: Component, apply: Component => Unit): Unit = {
    def traverse(comp: Component): Unit = {
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
    font.deriveFont(JMap.of(TextAttribute.TRANSFORM, new TransformAttribute(transform)))

  def font(family: String = Isabelle_Fonts.sans, size: Int = 1, bold: Boolean = false): Font =
    new Font(family, if (bold) Font.BOLD else Font.PLAIN, size)

  def label_font(): Font = (new JLabel).getFont


  /* Isabelle fonts */

  def imitate_font(
    font: Font,
    family: String = Isabelle_Fonts.sans,
    scale: Double = 1.0
  ): Font = {
    val font1 = new Font(family, font.getStyle, font.getSize)
    val rel_size = line_metrics(font).getHeight.toDouble / line_metrics(font1).getHeight
    new Font(family, font.getStyle, (scale * rel_size * font.getSize).toInt)
  }

  def imitate_font_css(
    font: Font,
    family: String = Isabelle_Fonts.sans,
    scale: Double = 1.0
  ): String = {
    val font1 = new Font(family, font.getStyle, font.getSize)
    val rel_size = line_metrics(font).getHeight.toDouble / line_metrics(font1).getHeight
    "font-family: " + family + "; font-size: " + (scale * rel_size * 100).toInt + "%;"
  }

  def use_isabelle_fonts(): Unit = {
    val default_font = label_font()
    val ui = UIManager.getDefaults
    for (prop <-
      List(
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
        "Tree.font")) {
      val font = ui.get(prop) match { case font: Font => font case _ => default_font }
      ui.put(prop, GUI.imitate_font(font))
    }
  }
}

class FlatLightLaf extends GUI.Look_And_Feel(new com.formdev.flatlaf.FlatLightLaf)
class FlatDarkLaf extends GUI.Look_And_Feel(new com.formdev.flatlaf.FlatDarkLaf)
