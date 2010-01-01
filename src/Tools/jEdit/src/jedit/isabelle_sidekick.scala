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

import isabelle.proofdocument.{Command, Markup_Node, Document}


class Isabelle_Sidekick extends SideKickParser("isabelle")
{
  /* parsing */

  @volatile private var stopped = false
  override def stop() = { stopped = true }

  def parse(buffer: Buffer, error_source: DefaultErrorSource): SideKickParsedData =
  {
    implicit def int_to_pos(offset: Int): Position =
      new Position { def getOffset = offset; override def toString = offset.toString }

    stopped = false

    // FIXME lock buffer !??
    val data = new SideKickParsedData(buffer.getName)
    val root = data.root
    data.getAsset(root).setEnd(buffer.getLength)

    Swing_Thread.now { Document_Model(buffer) } match {
      case Some(model) =>
        val document = model.current_document()
        for (command <- document.commands if !stopped) {
          root.add(command.markup_root(document).swing_tree((node: Markup_Node) =>
              {
                val content = command.content(node.start, node.stop)
                val command_start = command.start(document)
                val id = command.id

                new DefaultMutableTreeNode(new IAsset {
                  override def getIcon: Icon = null
                  override def getShortString: String = content
                  override def getLongString: String = node.info.toString
                  override def getName: String = id
                  override def setName(name: String) = ()
                  override def setStart(start: Position) = ()
                  override def getStart: Position = command_start + node.start
                  override def setEnd(end: Position) = ()
                  override def getEnd: Position = command_start + node.stop
                  override def toString = id + ": " + content + "[" + getStart + " - " + getEnd + "]"
                })
              }))
        }
        if (stopped) root.add(new DefaultMutableTreeNode("<parser stopped>"))
      case None => root.add(new DefaultMutableTreeNode("<buffer inactive>"))
    }
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

    val completion = Isabelle.session.current_syntax.completion

    completion.complete(text) match {
      case None => null
      case Some((word, cs)) =>
        val ds =
          if (Isabelle_Encoding.is_active(buffer))
            cs.map(Isabelle.system.symbols.decode(_)).sort(_ < _)
          else cs
        new SideKickCompletion(pane.getView, word, ds.toArray.asInstanceOf[Array[Object]]) { }
    }
  }

}
