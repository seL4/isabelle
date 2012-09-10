/*  Title:      Tools/jEdit/src/jedit_options.scala
    Author:     Makarius

Options for Isabelle/jEdit.
*/

package isabelle.jedit


import isabelle._


class JEdit_Options extends Options_Variable
{
  def title(name: String): String = value.title("jedit", name)
  def description(name: String): String = value.description(name)
}

