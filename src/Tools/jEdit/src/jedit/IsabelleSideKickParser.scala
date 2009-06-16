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

import org.gjt.sp.jedit.{Buffer, EditPane, TextUtilities, View}
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
          data.root.add(command.markup_root.swing_node(document))
        
        if (stopped) data.root.add(new DefaultMutableTreeNode("<parser stopped>"))
    } else {
      data.root.add(new DefaultMutableTreeNode("<buffer inactive>"))
    }

    data
  }


  /* completion */

  override def supportsCompletion = true
  override def canCompleteAnywhere = true

  override def complete(pane: EditPane, caret: Int): SideKickCompletion =
  {
    val buffer = pane.getBuffer
    val ps = Isabelle.prover_setup(buffer)
    if (ps.isDefined) {
      val no_word_sep = "_'.?"

      val caret_line = buffer.getLineOfOffset(caret)
      val line = buffer.getLineSegment(caret_line)

      val dot = caret - buffer.getLineStartOffset(caret_line)
      if (dot == 0) return null

      val ch = line.charAt(dot - 1)
      if (!ch.isLetterOrDigit &&   // FIXME Isabelle word!?
          no_word_sep.indexOf(ch) == -1) return null

		  val word_start = TextUtilities.findWordStart(line, dot - 1, no_word_sep)
      val word = line.subSequence(word_start, dot)
  		if (word.length <= 1) return null   // FIXME property?

      val completions = ps.get.prover.completions(word).filter(_ != word)
      if (completions.isEmpty) return null

      new SideKickCompletion(pane.getView, word.toString,
        completions.toArray.asInstanceOf[Array[Object]]) {}
    } else null
  }

}
