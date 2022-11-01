/*  Title:      Tools/jEdit/src/jedit_options.scala
    Author:     Makarius

Options for Isabelle/jEdit.
*/

package isabelle.jedit


import isabelle._

import java.awt.{Font, Color}
import javax.swing.{InputVerifier, JComponent, UIManager}
import javax.swing.text.JTextComponent

import scala.swing.{Component, CheckBox, TextArea}

import org.gjt.sp.jedit.gui.ColorWellButton


trait Option_Component extends Component {
  val title: String
  def load(): Unit
  def save(): Unit
}

object JEdit_Options {
  /* sections */

  val RENDERING_SECTION = "Rendering of Document Content"


  /* typed access and GUI components */

  class Access[A](access: Options.Access_Variable[A], val name: String) {
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

  object skip_proofs extends Bool_Access("skip_proofs") {
    override def changed(): Unit = GUI_Thread.require {
      super.changed()
      PIDE.editor.flush_edits(hidden = true)
      PIDE.editor.flush()
    }

    class GUI extends Bool_GUI(this, "Skip proofs") {
      tooltip = "Avoid checking proofs where possible"
    }
  }

  object defer_proofs extends Bool_Access("defer_proofs") {
    override def changed(): Unit = GUI_Thread.require {
      super.changed()
      PIDE.editor.flush_edits(hidden = true)
      PIDE.editor.flush()
    }

    class GUI extends Bool_GUI(this, "Defer proofs") {
      tooltip = "Defer proof checking"
    }
  }

  object quick_print extends Bool_Access("quick_print") {
    override def changed(): Unit = GUI_Thread.require {
      super.changed()
      PIDE.editor.flush_edits(hidden = true)
      PIDE.editor.flush()
    }

    class GUI extends Bool_GUI(this, "Quick print") {
      tooltip = "Skip typed print translations"
    }
  }
}

class JEdit_Options(init_options: Options) extends Options_Variable(init_options) {
  def color_value(s: String): Color = Color_Value(string(s))

  def make_color_component(opt: Options.Opt): Option_Component = {
    GUI_Thread.require {}

    val opt_name = opt.name
    val opt_title = opt.title("jedit")

    val button = new ColorWellButton(Color_Value(opt.value))
    val component = new Component with Option_Component {
      override lazy val peer: JComponent = button
      name = opt_name
      val title: String = opt_title
      def load(): Unit = button.setSelectedColor(Color_Value(string(opt_name)))
      def save(): Unit = string(opt_name) = Color_Value.print(button.getSelectedColor)
    }
    component.tooltip = GUI.tooltip_lines(opt.print_default)
    component
  }

  def make_component(opt: Options.Opt): Option_Component = {
    GUI_Thread.require {}

    val opt_name = opt.name
    val opt_title = opt.title("jedit")

    val component =
      if (opt.typ == Options.Bool)
        new CheckBox with Option_Component {
          name = opt_name
          val title: String = opt_title
          def load(): Unit = selected = bool(opt_name)
          def save(): Unit = bool(opt_name) = selected
        }
      else {
        val default_font = GUI.copy_font(UIManager.getFont("TextField.font"))
        val text_area =
          new TextArea with Option_Component {
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
              try { value + (opt_name, text.getText); true }
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
    predefined: List[Option_Component],
    filter: String => Boolean
  ) : List[(String, List[Option_Component])] = {
    def mk_component(opt: Options.Opt): List[Option_Component] =
      predefined.find(opt.name == _.name) match {
        case Some(c) => List(c)
        case None => if (filter(opt.name)) List(make_component(opt)) else Nil
      }
    value.sections.sortBy(_._1).map(
        { case (a, opts) => (a, opts.sortBy(_.title("jedit")).flatMap(mk_component)) })
      .filterNot(_._2.isEmpty)
  }
}

