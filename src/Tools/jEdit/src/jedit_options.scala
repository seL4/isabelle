/*  Title:      Tools/jEdit/src/jedit_options.scala
    Author:     Makarius

Options for Isabelle/jEdit.
*/

package isabelle.jedit


import isabelle._

import java.awt.Color
import javax.swing.{InputVerifier, JComponent, UIManager}
import javax.swing.text.JTextComponent

import scala.swing.{Component, CheckBox, TextArea}

import org.gjt.sp.jedit.gui.ColorWellButton
import org.gjt.sp.jedit.{jEdit, AbstractOptionPane}


object JEdit_Options {
  /* typed access and GUI components */

  class Access[A](access: Options.Access_Variable[A], val name: String) {
    def description: String = access.options.value.description(name)
    def apply(): A = access.apply(name)
    def update(x: A): Unit = change(_ => x)
    def change(f: A => A): Unit = {
      val x0 = apply()
      access.change(name, f)
      val x1 = apply()
      if (x0 != x1) changed()
    }
    def changed(): Unit = GUI_Thread.require { PIDE.session.update_options(access.options.value) }
  }

  class Bool_Access(name: String) extends Access(PIDE.options.bool, name) {
    def set(): Unit = update(true)
    def reset(): Unit = update(false)
    def toggle(): Unit = change(b => !b)
  }

  class Bool_GUI(access: Bool_Access, label: String)
  extends GUI.Check(label, init = access()) {
    def load(): Unit = { selected = access() }
    override def clicked(state: Boolean): Unit = access.update(state)
  }


  /* specific options */

  object continuous_checking extends Bool_Access("editor_continuous_checking") {
    override def changed(): Unit = {
      super.changed()
      PIDE.plugin.deps_changed()
    }

    class GUI extends Bool_GUI(this, "Continuous checking") {
      tooltip = "Continuous checking of proof document (visible and required parts)"
    }
  }

  object output_state extends Bool_Access("editor_output_state") {
    override def changed(): Unit = GUI_Thread.require {
      super.changed()
      PIDE.editor.flush_edits(hidden = true)
      PIDE.editor.flush()
    }

    class GUI extends Bool_GUI(this, "Proof state") {
      tooltip = "Output of proof state (normally shown on State panel)"
    }
  }

  object auto_hovering extends Bool_Access("editor_auto_hovering") {
    class GUI extends Bool_GUI(this, "Auto hovering") {
      tooltip = "Automatic mouse hovering without keyboard modifier"
    }
  }


  /* editor pane for plugin options */

  trait Entry extends Component {
    val title: String
    def load(): Unit
    def save(): Unit
  }

  abstract class Isabelle_Options(name: String) extends AbstractOptionPane(name) {
    protected val components: List[(String, List[Entry])]

    override def _init(): Unit = {
      val dummy_property = "options.isabelle.dummy"

      for ((s, cs) <- components) {
        if (s.nonEmpty) {
          jEdit.setProperty(dummy_property, s)
          addSeparator(dummy_property)
          jEdit.setProperty(dummy_property, null)
        }
        for (c <- cs) addComponent(c.title, c.peer)
      }
    }

    override def _save(): Unit = {
      for ((_, cs) <- components; c <- cs) c.save()
    }
  }

  class Isabelle_General_Options extends Isabelle_Options("isabelle-general") {
    val options: JEdit_Options = PIDE.options

    private val predefined =
      List(
        JEdit_Sessions.logic_selector(options),
        JEdit_Sessions.document_selector(options),
        JEdit_Spell_Checker.dictionaries_selector())

    protected val components: List[(String, List[Entry])] =
      options.make_components(predefined,
        (for (opt <- options.value.iterator if opt.public) yield opt.name).toSet)
  }

  class Isabelle_Rendering_Options extends Isabelle_Options("isabelle-rendering") {
    private val is_dark = GUI.is_dark_laf()

    private val predefined =
      (for {
        opt <- PIDE.options.value.iterator
        if opt.for_color_dialog && opt.is_dark == is_dark
      } yield PIDE.options.make_color_component(opt)).toList

    assert(predefined.nonEmpty)

    protected val components: List[(String, List[Entry])] =
      PIDE.options.make_components(predefined, _ => false)
  }
}

class JEdit_Options(init_options: Options) extends Options_Variable(init_options) {
  def color_value(s: String): Color = Color_Value(string(s + Options.theme_suffix()))

  def make_color_component(opt: Options.Entry): JEdit_Options.Entry = {
    GUI_Thread.require {}

    val opt_name = opt.name
    val opt_title = opt.title_jedit

    val button = new ColorWellButton(Color_Value(opt.value))
    val component =
      new Component with JEdit_Options.Entry {
        override lazy val peer: JComponent = button
        name = opt_name
        val title: String = opt_title
        def load(): Unit = button.setSelectedColor(Color_Value(string(opt_name)))
        def save(): Unit = string(opt_name) = Color_Value.print(button.getSelectedColor)
      }
    component.tooltip = GUI.tooltip_lines(opt.print_default)
    component
  }

  def make_component(opt: Options.Entry): JEdit_Options.Entry = {
    GUI_Thread.require {}

    val opt_name = opt.name
    val opt_title = opt.title_jedit

    val component =
      if (opt.typ == Options.Bool)
        new CheckBox with JEdit_Options.Entry {
          name = opt_name
          val title: String = opt_title
          def load(): Unit = selected = bool(opt_name)
          def save(): Unit = bool(opt_name) = selected
        }
      else {
        val default_font = GUI.copy_font(UIManager.getFont("TextField.font"))
        val text_area =
          new TextArea with JEdit_Options.Entry {
            if (default_font != null) font = default_font
            name = opt_name
            val title: String = opt_title
            def load(): Unit = text = value.check_name(opt_name).value
            def save(): Unit =
              try { JEdit_Options.this += (opt_name, text) }
              catch {
                case ERROR(msg) =>
                  GUI.error_dialog(this.peer, "Failed to update options",
                    GUI.scrollable_text(msg))
              }
          }
        text_area.peer.setInputVerifier({
            case text: JTextComponent =>
              try { value + Options.Spec.eq(opt_name, text.getText); true }
              catch { case ERROR(_) => false }
            case _ => true
          })
        GUI.plain_focus_traversal(text_area.peer)
        text_area
      }
    component.load()
    component.tooltip = GUI.tooltip_lines(opt.print_default)
    component
  }

  def make_components(
    predefined: List[JEdit_Options.Entry],
    filter: String => Boolean
  ) : List[(String, List[JEdit_Options.Entry])] = {
    def mk_component(opt: Options.Entry): List[JEdit_Options.Entry] =
      predefined.find(opt.name == _.name) match {
        case Some(c) => List(c)
        case None => if (filter(opt.name)) List(make_component(opt)) else Nil
      }
    value.sections.sortBy(_._1).map(
        { case (a, opts) => (a, opts.sortBy(_.title_jedit).flatMap(mk_component)) })
      .filterNot(_._2.isEmpty)
  }
}
