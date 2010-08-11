/*  Title:      Tools/jEdit/src/jedit/isabelle_sidekick.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

SideKick parsers for Isabelle proof documents.
*/

package isabelle.jedit


import isabelle._

import scala.collection.Set
import scala.collection.immutable.TreeSet

import javax.swing.tree.DefaultMutableTreeNode
import javax.swing.text.Position
import javax.swing.Icon

import org.gjt.sp.jedit.{Buffer, EditPane, TextUtilities, View}
import errorlist.DefaultErrorSource
import sidekick.{SideKickParser, SideKickParsedData, SideKickCompletion, IAsset}


object Isabelle_Sidekick
{
  implicit def int_to_pos(offset: Int): Position =
    new Position { def getOffset = offset; override def toString = offset.toString }
}


abstract class Isabelle_Sidekick(name: String) extends SideKickParser(name)
{
  /* parsing */

  @volatile protected var stopped = false
  override def stop() = { stopped = true }

  def parser(data: SideKickParsedData, model: Document_Model): Unit

  def parse(buffer: Buffer, error_source: DefaultErrorSource): SideKickParsedData =
  {
    import Isabelle_Sidekick.int_to_pos

    stopped = false

    // FIXME lock buffer !??
    val data = new SideKickParsedData(buffer.getName)
    val root = data.root
    data.getAsset(root).setEnd(buffer.getLength)

    Swing_Thread.now { Document_Model(buffer) } match {
      case Some(model) =>
        parser(data, model)
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
          (if (Isabelle_Encoding.is_active(buffer))
            cs.map(Isabelle.system.symbols.decode(_)).sort(_ < _)
           else cs).filter(_ != word)
        if (ds.isEmpty) null
        else new SideKickCompletion(pane.getView, word, ds.toArray.asInstanceOf[Array[Object]]) { }
    }
  }
}


class Isabelle_Sidekick_Default extends Isabelle_Sidekick("isabelle")
{
  def parser(data: SideKickParsedData, model: Document_Model)
  {
    import Isabelle_Sidekick.int_to_pos

    val root = data.root
    val doc = Swing_Thread.now { model.snapshot().node }  // FIXME cover all nodes (!??)
    for {
      (command, command_start) <- doc.command_range(0)
      if command.is_command && !stopped
    }
    {
      val name = command.name
      val node =
        new DefaultMutableTreeNode(new IAsset {
          override def getIcon: Icon = null
          override def getShortString: String = name
          override def getLongString: String = name
          override def getName: String = name
          override def setName(name: String) = ()
          override def setStart(start: Position) = ()
          override def getStart: Position = command_start
          override def setEnd(end: Position) = ()
          override def getEnd: Position = command_start + command.length
          override def toString = name
        })
      root.add(node)
    }
  }
}


class Isabelle_Sidekick_Raw extends Isabelle_Sidekick("isabelle-raw")
{
  def parser(data: SideKickParsedData, model: Document_Model)
  {
    import Isabelle_Sidekick.int_to_pos

    val root = data.root
    val snapshot = Swing_Thread.now { model.snapshot() }  // FIXME cover all nodes (!??)
    for ((command, command_start) <- snapshot.node.command_range(0) if !stopped) {
      root.add(snapshot.state(command).markup_root.swing_tree((node: Markup_Node) =>
          {
            val content = command.source(node.start, node.stop).replace('\n', ' ')
            val id = command.id

            new DefaultMutableTreeNode(new IAsset {
              override def getIcon: Icon = null
              override def getShortString: String = content
              override def getLongString: String = node.info.toString
              override def getName: String = Document.print_id(id)
              override def setName(name: String) = ()
              override def setStart(start: Position) = ()
              override def getStart: Position = command_start + node.start
              override def setEnd(end: Position) = ()
              override def getEnd: Position = command_start + node.stop
              override def toString = id + ": " + content + "[" + getStart + " - " + getEnd + "]"
            })
          }))
    }
  }
}

