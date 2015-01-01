/*  Title:      Tools/Graphview/mutator_dialog.scala
    Author:     Markus Kaiser, TU Muenchen

Mutator selection and configuration dialog.
*/

package isabelle.graphview


import isabelle._

import java.awt.Color
import java.awt.FocusTraversalPolicy
import javax.swing.JColorChooser
import javax.swing.border.EmptyBorder
import scala.collection.JavaConversions._
import scala.swing._
import scala.swing.event.ValueChanged


class Mutator_Dialog(
    visualizer: Visualizer,
    container: Mutator_Container,
    caption: String,
    reverse_caption: String = "Inverse",
    show_color_chooser: Boolean = true)
  extends Dialog
{
  title = caption

  private var _panels: List[Mutator_Panel] = Nil
  private def panels = _panels
  private def panels_=(panels: List[Mutator_Panel])
  {
    _panels = panels
    paintPanels
  }

  container.events +=
  {
    case Mutator_Event.Add(m) => addPanel(new Mutator_Panel(m))
    case Mutator_Event.New_List(ms) => panels = get_panels(ms)
  }

  override def open()
  {
    if (!visible) panels = get_panels(container())
    super.open
  }

  minimumSize = new Dimension(700, 200)
  preferredSize = new Dimension(1000, 300)
  peer.setFocusTraversalPolicy(Focus_Traversal)

  private def get_panels(m: List[Mutator.Info]): List[Mutator_Panel] =
    m.filter({ case Mutator.Info(_, _, Mutator.Identity()) => false case _ => true })
    .map(m => new Mutator_Panel(m))

  private def get_mutators(panels: List[Mutator_Panel]): List[Mutator.Info] =
    panels.map(panel => panel.get_mutator)

  private def movePanelUp(m: Mutator_Panel) =
  {
    def moveUp(l: List[Mutator_Panel]): List[Mutator_Panel] =
      l match {
        case x :: y :: xs => if (y == m) y :: x :: xs else x :: moveUp(y :: xs)
        case _ => l
      }

    panels = moveUp(panels)
  }

  private def movePanelDown(m: Mutator_Panel) =
  {
    def moveDown(l: List[Mutator_Panel]): List[Mutator_Panel] =
      l match {
        case x :: y :: xs => if (x == m) y :: x :: xs else x :: moveDown(y :: xs)
        case _ => l
      }

    panels = moveDown(panels)
  }

  private def removePanel(m: Mutator_Panel)
  {
    panels = panels.filter(_ != m).toList
  }

  private def addPanel(m: Mutator_Panel)
  {
    panels = panels ::: List(m)
  }

  def paintPanels
  {
    Focus_Traversal.clear
    filterPanel.contents.clear
    panels.map(x => {
        filterPanel.contents += x
        Focus_Traversal.addAll(x.focusList)
      })
    filterPanel.contents += Swing.VGlue

    Focus_Traversal.add(mutator_box.peer.asInstanceOf[java.awt.Component])
    Focus_Traversal.add(add_button.peer)
    Focus_Traversal.add(apply_button.peer)
    Focus_Traversal.add(cancel_button.peer)
    filterPanel.revalidate
    filterPanel.repaint
  }

  val filterPanel = new BoxPanel(Orientation.Vertical) {}

  private val mutator_box = new ComboBox[Mutator](container.available)

  private val add_button: Button = new Button {
    action = Action("Add") {
      addPanel(
        new Mutator_Panel(Mutator.Info(true, visualizer.Colors.next, mutator_box.selection.item)))
    }
  }

  private val apply_button = new Button {
    action = Action("Apply") { container(get_mutators(panels)) }
  }

  private val reset_button = new Button {
    action = Action("Reset") { panels = get_panels(container()) }
  }

  private val cancel_button = new Button {
    action = Action("Close") { close }
  }
  defaultButton = cancel_button

  private val botPanel = new BoxPanel(Orientation.Horizontal) {
    border = new EmptyBorder(10, 0, 0, 0)

    contents += mutator_box
    contents += Swing.RigidBox(new Dimension(10, 0))
    contents += add_button

    contents += Swing.HGlue
    contents += Swing.RigidBox(new Dimension(30, 0))
    contents += apply_button

    contents += Swing.RigidBox(new Dimension(5, 0))
    contents += reset_button

    contents += Swing.RigidBox(new Dimension(5, 0))
    contents += cancel_button
  }

  contents = new BorderPanel {
    border = new EmptyBorder(5, 5, 5, 5)

    add(new ScrollPane(filterPanel), BorderPanel.Position.Center)
    add(botPanel, BorderPanel.Position.South)
  }

  private class Mutator_Panel(initials: Mutator.Info)
    extends BoxPanel(Orientation.Horizontal)
  {
    private val inputs: List[(String, Mutator_Input_Value)] = get_Inputs()
    var focusList = List.empty[java.awt.Component]
    private val enabledBox = new iCheckBox("Enabled", initials.enabled)

    border = new EmptyBorder(5, 5, 5, 5)
    maximumSize = new Dimension(Integer.MAX_VALUE, 30)
    background = initials.color

    contents += new Label(initials.mutator.name) {
      preferredSize = new Dimension(175, 20)
      horizontalAlignment = Alignment.Left
      if (initials.mutator.description != "") tooltip = initials.mutator.description
    }
    contents += Swing.RigidBox(new Dimension(10, 0))
    contents += enabledBox
    contents += Swing.RigidBox(new Dimension(5, 0))
    focusList = enabledBox.peer :: focusList
    inputs.map(_ match {
      case (n, c) =>
        contents += Swing.RigidBox(new Dimension(10, 0))
        if (n != "") {
          contents += new Label(n)
          contents += Swing.RigidBox(new Dimension(5, 0))
        }
        contents += c.asInstanceOf[Component]

        focusList = c.asInstanceOf[Component].peer :: focusList
      case _ =>
    })

    {
      val t = this
      contents += Swing.HGlue
      contents += Swing.RigidBox(new Dimension(10, 0))

      if (show_color_chooser) {
        contents += new Button {
          maximumSize = new Dimension(20, 20)

          action = Action("Color") {
            t.background =
              JColorChooser.showDialog(t.peer, "Choose new Color", t.background)
          }

          focusList = this.peer :: focusList
        }
        contents += Swing.RigidBox(new Dimension(2, 0))
      }

      contents += new Button {
        maximumSize = new Dimension(20, 20)

        action = Action("Up") {
          movePanelUp(t)
        }

        focusList = this.peer :: focusList
      }
      contents += Swing.RigidBox(new Dimension(2, 0))
      contents += new Button {
        maximumSize = new Dimension(20, 20)

        action = Action("Down") {
          movePanelDown(t)
        }

        focusList = this.peer :: focusList
      }
      contents += Swing.RigidBox(new Dimension(2, 0))
      contents += new Button {
        maximumSize = new Dimension(20, 20)

        action = Action("Del") {
          removePanel(t)
        }

        focusList = this.peer :: focusList
      }
    }

    focusList = focusList.reverse

    private def isRegex(regex: String): Boolean =
    {
      try { regex.r; true }
      catch { case _: java.util.regex.PatternSyntaxException =>  false }
    }

    def get_mutator: Mutator.Info =
    {
      def regexOrElse(regex: String, orElse: String): String =
      {
        if (isRegex(regex)) regex
        else orElse
      }

      val m =
        initials.mutator match {
          case Mutator.Identity() =>
            Mutator.Identity()
          case Mutator.Node_Expression(r, _, _, _) =>
            Mutator.Node_Expression(
              regexOrElse(inputs(2)._2.getString, r),
              inputs(3)._2.getBool,
              // "Parents" means "Show parents" or "Matching Children"
              inputs(1)._2.getBool,
              inputs(0)._2.getBool)
          case Mutator.Node_List(_, _, _, _) =>
            Mutator.Node_List(
              inputs(2)._2.getString.split(',').filter(_ != "").toList,
              inputs(3)._2.getBool,
              // "Parents" means "Show parents" or "Matching Children"
              inputs(1)._2.getBool,
              inputs(0)._2.getBool)
          case Mutator.Edge_Endpoints(_, _) =>
            Mutator.Edge_Endpoints(
              inputs(0)._2.getString,
              inputs(1)._2.getString)
          case Mutator.Add_Node_Expression(r) =>
            Mutator.Add_Node_Expression(regexOrElse(inputs(0)._2.getString, r))
          case Mutator.Add_Transitive_Closure(_, _) =>
            Mutator.Add_Transitive_Closure(
              inputs(0)._2.getBool,
              inputs(1)._2.getBool)
          case _ =>
            Mutator.Identity()
        }

      Mutator.Info(enabledBox.selected, background, m)
    }

    private def get_Inputs(): List[(String, Mutator_Input_Value)] =
      initials.mutator match {
        case Mutator.Node_Expression(regex, reverse, check_parents, check_children) =>
          List(
            ("", new iCheckBox("Parents", check_children)),
            ("", new iCheckBox("Children", check_parents)),
            ("Regex", new iTextField(regex, x => !isRegex(x))),
            ("", new iCheckBox(reverse_caption, reverse)))
        case Mutator.Node_List(list, reverse, check_parents, check_children) =>
          List(
            ("", new iCheckBox("Parents", check_children)),
            ("", new iCheckBox("Children", check_parents)),
            ("Names", new iTextField(list.mkString(","))),
            ("", new iCheckBox(reverse_caption, reverse)))
        case Mutator.Edge_Endpoints(source, dest) =>
          List(
            ("Source", new iTextField(source)),
            ("Destination", new iTextField(dest)))
        case Mutator.Add_Node_Expression(regex) =>
          List(("Regex", new iTextField(regex, x => !isRegex(x))))
        case Mutator.Add_Transitive_Closure(parents, children) =>
          List(
            ("", new iCheckBox("Parents", parents)),
            ("", new iCheckBox("Children", children)))
        case _ => Nil
      }
  }

  private trait Mutator_Input_Value
  {
    def getString: String
    def getBool: Boolean
  }

  private class iTextField(t: String, colorator: String => Boolean)
  extends TextField(t) with Mutator_Input_Value
  {
    def this(t: String) = this(t, x => false)

    preferredSize = new Dimension(125, 18)

    reactions +=
    {
      case ValueChanged(_) =>
        if (colorator(text)) background = Color.RED
        else background = Color.WHITE
    }

    def getString = text
    def getBool = true
  }

  private class iCheckBox(t: String, s: Boolean)
  extends CheckBox(t) with Mutator_Input_Value
  {
    selected = s

    def getString = ""
    def getBool = selected
  }

  private object Focus_Traversal extends FocusTraversalPolicy
  {
    private var items = Vector[java.awt.Component]()

    def add(c: java.awt.Component) { items = items :+ c }
    def addAll(cs: TraversableOnce[java.awt.Component]) { items = items ++ cs }
    def clear() { items = Vector[java.awt.Component]() }

    def getComponentAfter(root: java.awt.Container, c: java.awt.Component): java.awt.Component =
    {
      val i = items.indexOf(c)
      if (i < 0) getDefaultComponent(root)
      else items((i + 1) % items.length)
    }

    def getComponentBefore(root: java.awt.Container, c: java.awt.Component): java.awt.Component =
    {
      val i = items.indexOf(c)
      if (i < 0) getDefaultComponent(root)
      else items((i - 1) % items.length)
    }

    def getFirstComponent(root: java.awt.Container): java.awt.Component =
      if (items.length > 0) items(0) else null

    def getDefaultComponent(root: java.awt.Container): java.awt.Component =
      getFirstComponent(root)

    def getLastComponent(root: java.awt.Container): java.awt.Component =
      if (items.length > 0) items.last else null
  }
}