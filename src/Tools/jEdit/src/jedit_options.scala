/*  Title:      Tools/jEdit/src/jedit_options.scala
    Author:     Makarius

Options for Isabelle/jEdit.
*/

package isabelle.jedit


import isabelle._

import javax.swing.{InputVerifier, JComponent}
import javax.swing.text.JTextComponent
import scala.swing.{Component, CheckBox, TextArea}


trait Option_Component extends Component
{
  val title: String
  def load(): Unit
  def save(): Unit
}

class JEdit_Options extends Options_Variable
{
  def title(opt_name: String): String = value.title("jedit", opt_name)

  def make_component(opt_name: String): Option_Component =
  {
    Swing_Thread.require()

    val opt = value.check_name(opt_name)
    val opt_title = title(opt_name)

    val component =
      if (opt.typ == Options.Bool)
        new CheckBox with Option_Component {
          val title = opt_title
          def load = selected = bool(opt_name)
          def save = bool(opt_name) = selected
        }
      else {
        val text_area =
          new TextArea with Option_Component {
            val title = opt_title
            def load = text = value.check_name(opt_name).value
            def save = update(value + (opt_name, text))
          }
        text_area.peer.setInputVerifier(new InputVerifier {
          def verify(jcomponent: JComponent): Boolean =
            jcomponent match {
              case text: JTextComponent =>
                try { value + (opt_name, text.getText); true }
                catch { case ERROR(_) => false }
              case _ => true
            }
          })
        text_area
      }
    component.load()
    component.tooltip = opt.print
    component
  }
}

