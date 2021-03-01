/*  Title:      Tools/Graphview/mutator_dialog.scala
    Author:     Markus Kaiser, TU Muenchen
    Author:     Makarius

Mutator selection and configuration dialog.
*/

package isabelle.graphview


import isabelle._

import java.awt.Color
import java.awt.FocusTraversalPolicy
import javax.swing.JColorChooser
import javax.swing.border.EmptyBorder
import scala.swing.{Dialog, Button, BoxPanel, Swing, Orientation, ComboBox, Action,
  Dimension, BorderPanel, ScrollPane, Label, CheckBox, Alignment, Component, TextField}
import scala.swing.event.ValueChanged


class Mutator_Dialog(
    graphview: Graphview,
    container: Mutator_Container,
    caption: String,
    reverse_caption: String = "Inverse",
    show_color_chooser: Boolean = true)
  extends Dialog
{
  title = caption

  private var _panels: List[Mutator_Panel] = Nil
  private def panels = _panels
  private def panels_=(panels: List[Mutator_Panel]): Unit =
  {
    _panels = panels
    paint_panels()
  }

  container.events +=
  {
    case Mutator_Event.Add(m) => add_panel(new Mutator_Panel(m))
    case Mutator_Event.New_List(ms) => panels = get_panels(ms)
  }

  override def open(): Unit =
  {
    if (!visible) panels = get_panels(container())
    super.open
  }

  minimumSize = new Dimension(700, 200)
  preferredSize = new Dimension(1000, 300)
  peer.setFocusTraversalPolicy(Focus_Traveral_Policy)

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

  private def removePanel(m: Mutator_Panel): Unit =
  {
    panels = panels.filter(_ != m).toList
  }

  private def add_panel(m: Mutator_Panel): Unit =
  {
    panels = panels ::: List(m)
  }

  def paint_panels(): Unit =
  {
    Focus_Traveral_Policy.clear
    filter_panel.contents.clear
    panels.map(x => {
        filter_panel.contents += x
        Focus_Traveral_Policy.addAll(x.focusList)
      })
    filter_panel.contents += Swing.VGlue

    Focus_Traveral_Policy.add(mutator_box.peer.asInstanceOf[java.awt.Component])
    Focus_Traveral_Policy.add(add_button.peer)
    Focus_Traveral_Policy.add(apply_button.peer)
    Focus_Traveral_Policy.add(cancel_button.peer)
    filter_panel.revalidate
    filter_panel.repaint
  }

  val filter_panel: BoxPanel = new BoxPanel(Orientation.Vertical) {}

  private val mutator_box = new ComboBox[Mutator](container.available)

  private val add_button = new Button {
    action = Action("Add") {
      add_panel(
        new Mutator_Panel(Mutator.Info(true, graphview.Colors.next(), mutator_box.selection.item)))
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

    layout(new ScrollPane(filter_panel)) = BorderPanel.Position.Center
    layout(botPanel) = BorderPanel.Position.South
  }

  private class Mutator_Panel(initials: Mutator.Info)
    extends BoxPanel(Orientation.Horizontal)
  {
    private val inputs: List[(String, Input)] = get_inputs()
    var focusList = List.empty[java.awt.Component]
    private val enabledBox = new Check_Box_Input("Enabled", initials.enabled)

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
    inputs.map({
      case (n, c) =>
        contents += Swing.RigidBox(new Dimension(10, 0))
        if (n != "") {
          contents += new Label(n)
          contents += Swing.RigidBox(new Dimension(5, 0))
        }
        contents += c.asInstanceOf[Component]

        focusList = c.asInstanceOf[Component].peer :: focusList
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

    def get_mutator: Mutator.Info =
    {
      val model = graphview.model
      val m =
        initials.mutator match {
          case Mutator.Identity() =>
            Mutator.Identity()
          case Mutator.Node_Expression(r, _, _, _) =>
            val r1 = inputs(2)._2.string
            Mutator.Node_Expression(
              if (Library.make_regex(r1).isDefined) r1 else r,
              inputs(3)._2.bool,
              // "Parents" means "Show parents" or "Matching Children"
              inputs(1)._2.bool,
              inputs(0)._2.bool)
          case Mutator.Node_List(_, _, _, _) =>
            Mutator.Node_List(
              for {
                ident <- space_explode(',', inputs(2)._2.string)
                node <- model.find_node(ident)
              } yield node,
              inputs(3)._2.bool,
              // "Parents" means "Show parents" or "Matching Children"
              inputs(1)._2.bool,
              inputs(0)._2.bool)
          case Mutator.Edge_Endpoints(_) =>
            (model.find_node(inputs(0)._2.string), model.find_node(inputs(1)._2.string)) match {
              case (Some(node1), Some(node2)) =>
                Mutator.Edge_Endpoints((node1, node2))
              case _ =>
                Mutator.Identity()
            }
          case Mutator.Add_Node_Expression(r) =>
            val r1 = inputs(0)._2.string
            Mutator.Add_Node_Expression(if (Library.make_regex(r1).isDefined) r1 else r)
          case Mutator.Add_Transitive_Closure(_, _) =>
            Mutator.Add_Transitive_Closure(
              inputs(0)._2.bool,
              inputs(1)._2.bool)
          case _ =>
            Mutator.Identity()
        }

      Mutator.Info(enabledBox.selected, background, m)
    }

    private def get_inputs(): List[(String, Input)] =
      initials.mutator match {
        case Mutator.Node_Expression(regex, reverse, check_parents, check_children) =>
          List(
            ("", new Check_Box_Input("Parents", check_children)),
            ("", new Check_Box_Input("Children", check_parents)),
            ("Regex", new Text_Field_Input(regex, x => Library.make_regex(x).isDefined)),
            ("", new Check_Box_Input(reverse_caption, reverse)))
        case Mutator.Node_List(list, reverse, check_parents, check_children) =>
          List(
            ("", new Check_Box_Input("Parents", check_children)),
            ("", new Check_Box_Input("Children", check_parents)),
            ("Names", new Text_Field_Input(list.map(_.ident).mkString(","))),
            ("", new Check_Box_Input(reverse_caption, reverse)))
        case Mutator.Edge_Endpoints((source, dest)) =>
          List(
            ("Source", new Text_Field_Input(source.ident)),
            ("Destination", new Text_Field_Input(dest.ident)))
        case Mutator.Add_Node_Expression(regex) =>
          List(("Regex", new Text_Field_Input(regex, x => Library.make_regex(x).isDefined)))
        case Mutator.Add_Transitive_Closure(parents, children) =>
          List(
            ("", new Check_Box_Input("Parents", parents)),
            ("", new Check_Box_Input("Children", children)))
        case _ => Nil
      }
  }

  private trait Input
  {
    def string: String
    def bool: Boolean
  }

  private class Text_Field_Input(txt: String, check: String => Boolean = (_: String) => true)
    extends TextField(txt) with Input
  {
    preferredSize = new Dimension(125, 18)

    private val default_foreground = foreground
    reactions +=
    {
      case ValueChanged(_) =>
        foreground = if (check(text)) default_foreground else graphview.error_color
    }

    def string = text
    def bool = true
  }

  private class Check_Box_Input(txt: String, s: Boolean) extends CheckBox(txt) with Input
  {
    selected = s

    def string = ""
    def bool = selected
  }

  private object Focus_Traveral_Policy extends FocusTraversalPolicy
  {
    private var items = Vector.empty[java.awt.Component]

    def add(c: java.awt.Component): Unit = { items = items :+ c }
    def addAll(cs: TraversableOnce[java.awt.Component]): Unit = { items = items ++ cs }
    def clear(): Unit = { items = Vector.empty }

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
      if (items.nonEmpty) items(0) else null

    def getDefaultComponent(root: java.awt.Container): java.awt.Component =
      getFirstComponent(root)

    def getLastComponent(root: java.awt.Container): java.awt.Component =
      if (items.nonEmpty) items.last else null
  }
}