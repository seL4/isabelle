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
import javax.swing.text.Position
import javax.swing.Icon

import org.gjt.sp.jedit.{Buffer, EditPane, TextUtilities, View}
import errorlist.DefaultErrorSource
import sidekick.{SideKickParser, SideKickParsedData, SideKickCompletion, IAsset}

import isabelle.prover.{Command, MarkupNode}
import isabelle.proofdocument.ProofDocument


class IsabelleSideKickParser extends SideKickParser("isabelle")
{
  /* parsing */

  @volatile private var stopped = false
  override def stop() = { stopped = true }

  def parse(buffer: Buffer, error_source: DefaultErrorSource): SideKickParsedData =
  {
    stopped = false

    val data = new SideKickParsedData(buffer.getName)

    val prover_setup = Isabelle.prover_setup(buffer)
    if (prover_setup.isDefined) {
      val document = prover_setup.get.theory_view.current_document()
      for (command <- document.commands if !stopped) {
        data.root.add(command.markup_root(document).
          swing_tree(document)((node: MarkupNode, cmd: Command, doc: ProofDocument) =>
            {
              implicit def int2pos(offset: Int): Position =
                new Position { def getOffset = offset; override def toString = offset.toString }

              new DefaultMutableTreeNode(new IAsset {
                override def getIcon: Icon = null
                override def getShortString: String = node.content
                override def getLongString: String = node.info.toString
                override def getName: String = node.id
                override def setName(name: String) = ()
                override def setStart(start: Position) = ()
                override def getStart: Position = node.abs_start(doc)
                override def setEnd(end: Position) = ()
                override def getEnd: Position = node.abs_stop(doc)
                override def toString =
                  node.id + ": " + node.content + "[" + getStart + " - " + getEnd + "]"
              })
            }))
      }
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
      Isabelle.prover_setup(buffer).map(_.prover.completion).getOrElse(Isabelle.completion)

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
