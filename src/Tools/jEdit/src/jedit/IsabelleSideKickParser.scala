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


class IsabelleSideKickParser extends SideKickParser("isabelle")
{
  /* parsing */

  @volatile private var stopped = false
  override def stop() = { stopped = true }

  def parse(buffer: Buffer, error_source: DefaultErrorSource): SideKickParsedData =
  {
    stopped = false

    val data = new SideKickParsedData(buffer.getName)

    val prover_setup = Isabelle.plugin.prover_setup(buffer)
    if (prover_setup.isDefined) {
      val document = prover_setup.get.theory_view.current_document()
      for (command <- document.commands)
        data.root.add(command.markup_root.swing_node(document))

      if (stopped) data.root.add(new DefaultMutableTreeNode("<parser stopped>"))
    }
    else data.root.add(new DefaultMutableTreeNode("<buffer inactive>"))

    data
  }


  /* completion */

  override def supportsCompletion = true
  override def canCompleteAnywhere = true

  override def complete(pane: EditPane, caret: Int): SideKickCompletion =
  {
    val buffer = pane.getBuffer

    val line = buffer.getLineOfOffset(caret)
    val start = buffer.getLineStartOffset(line)
    val text = buffer.getSegment(start, caret - start)

    val completion =
      Isabelle.prover_setup(buffer).map(_.prover.completion) getOrElse Isabelle.completion

    completion.complete(text) match {
      case None => null
      case Some((word, cs)) =>
        val ds =
          if (IsabelleEncoding.is_active(buffer))
            cs.map(Isabelle.system.symbols.decode(_)).sort(Completion.length_ord _)
          else cs
        new SideKickCompletion(pane.getView, word, ds.toArray.asInstanceOf[Array[Object]]) { }
    }
  }

}
