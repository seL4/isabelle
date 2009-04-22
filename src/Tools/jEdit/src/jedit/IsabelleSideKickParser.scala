/*
 * SideKick parser for Isabelle proof documents
 *
 * @author Fabian Immler, TU Munich
 * @author Makarius
 */

package isabelle.jedit

import scala.collection.Set
import scala.collection.immutable.TreeSet

import javax.swing.tree.DefaultMutableTreeNode

import org.gjt.sp.jedit.{Buffer, EditPane, View}
import errorlist.DefaultErrorSource
import sidekick.{SideKickParser, SideKickParsedData, SideKickCompletion}


class IsabelleSideKickParser extends SideKickParser("isabelle") {

  /* parsing */

  private var stopped = false
  override def stop() = { stopped = true }

  def parse(buffer : Buffer, error_source : DefaultErrorSource): SideKickParsedData = {
    stopped = false
    
    val data = new SideKickParsedData(buffer.getName)

    val prover_setup = Isabelle.plugin.prover_setup(buffer)
    if (prover_setup.isDefined) {
        val document = prover_setup.get.prover.document
        for (command <- document.commands)
          data.root.add(command.root_node.swing_node(document))
        
        if (stopped) data.root.add(new DefaultMutableTreeNode("<parser stopped>"))
    } else {
      data.root.add(new DefaultMutableTreeNode("<buffer inactive>"))
    }

    data
  }


  /* completion */

  override def supportsCompletion = true
  override def canCompleteAnywhere = true
  override def getInstantCompletionTriggers = "\\"

  override def complete(pane: EditPane, caret: Int): SideKickCompletion = null /*{
    val buffer = pane.getBuffer
    val ps = Isabelle.prover_setup(buffer)
    if (ps.isDefined) {
      val completions = ps.get.prover.completions
      def before_caret(i : Int) = buffer.getText(0 max caret - i, i)
      def next_nonfitting(s : String) : String = {
        val sa = s.toCharArray
        sa(s.length - 1) = (sa(s.length - 1) + 1).asInstanceOf[Char]
        new String(sa)
      }
      def suggestions(i : Int) : (Set[String], String)= {
        val text = before_caret(i)
        if (!text.matches("\\s") && i < 30) {
          val larger_results = suggestions(i + 1)
          if (larger_results._1.size > 0) larger_results
          else (completions.range(text, next_nonfitting(text)), text)
        } else (Set[String](), text)

      }

      val list = new java.util.LinkedList[String]
      val descriptions = new java.util.LinkedList[String]
      // compute suggestions
      val (suggs, text) = suggestions(1)
      for (s <- suggs) {
        val decoded = Isabelle.symbols.decode(s)
        list.add(decoded)
        if (decoded != s) descriptions.add(s) else descriptions.add(null)
      }
      return new IsabelleSideKickCompletion(pane.getView, text, list, descriptions)
    } else return null
  }*/

}

private class IsabelleSideKickCompletion(view: View, text: String,
                                         items: java.util.List[String],
                                         descriptions : java.util.List[String])
  extends SideKickCompletion(view, text, items : java.util.List[String]) {

  override def getCompletionDescription(i : Int) : String = descriptions.get(i)
}
