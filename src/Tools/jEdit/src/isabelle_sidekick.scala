/*  Title:      Tools/jEdit/src/isabelle_sidekick.scala
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
  def int_to_pos(offset: Text.Offset): Position =
    new Position { def getOffset = offset; override def toString = offset.toString }

  class Asset(name: String, start: Text.Offset, end: Text.Offset) extends IAsset
  {
    protected var _name = name
    protected var _start = int_to_pos(start)
    protected var _end = int_to_pos(end)
    override def getIcon: Icon = null
    override def getShortString: String = _name
    override def getLongString: String = _name
    override def getName: String = _name
    override def setName(name: String) = _name = name
    override def getStart: Position = _start
    override def setStart(start: Position) = _start = start
    override def getEnd: Position = _end
    override def setEnd(end: Position) = _end = end
    override def toString = _name
  }
}


abstract class Isabelle_Sidekick(name: String) extends SideKickParser(name)
{
  /* parsing */

  @volatile protected var stopped = false
  override def stop() = { stopped = true }

  def parser(data: SideKickParsedData, model: Document_Model): Unit

  def parse(buffer: Buffer, error_source: DefaultErrorSource): SideKickParsedData =
  {
    stopped = false

    // FIXME lock buffer (!??)
    val data = new SideKickParsedData(buffer.getName)
    val root = data.root
    data.getAsset(root).setEnd(Isabelle_Sidekick.int_to_pos(buffer.getLength))

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

  override def complete(pane: EditPane, caret: Text.Offset): SideKickCompletion =
  {
    val buffer = pane.getBuffer
    Isabelle.swing_buffer_lock(buffer) {
      Document_Model(buffer) match {
        case None => null
        case Some(model) =>
          val line = buffer.getLineOfOffset(caret)
          val start = buffer.getLineStartOffset(line)
          val text = buffer.getSegment(start, caret - start)

          val completion = model.session.current_syntax().completion
          completion.complete(text) match {
            case None => null
            case Some((word, cs)) =>
              val ds =
                (if (Isabelle_Encoding.is_active(buffer))
                  cs.map(Symbol.decode(_)).sorted
                 else cs).filter(_ != word)
              if (ds.isEmpty) null
              else new SideKickCompletion(
                pane.getView, word, ds.toArray.asInstanceOf[Array[Object]]) { }
          }
      }
    }
  }
}


class Isabelle_Sidekick_Default extends Isabelle_Sidekick("isabelle")
{
  import Thy_Syntax.Structure

  def parser(data: SideKickParsedData, model: Document_Model)
  {
    val syntax = model.session.current_syntax()

    def make_tree(offset: Text.Offset, entry: Structure.Entry): List[DefaultMutableTreeNode] =
      entry match {
        case Structure.Block(name, body) =>
          val node =
            new DefaultMutableTreeNode(
              new Isabelle_Sidekick.Asset(Library.first_line(name), offset, offset + entry.length))
          (offset /: body)((i, e) =>
            {
              make_tree(i, e) foreach (nd => node.add(nd))
              i + e.length
            })
          List(node)
        case Structure.Atom(command)
        if command.is_command && syntax.heading_level(command).isEmpty =>
          val node =
            new DefaultMutableTreeNode(
              new Isabelle_Sidekick.Asset(command.name, offset, offset + entry.length))
          List(node)
        case _ => Nil
      }

    val text = Isabelle.buffer_text(model.buffer)
    val structure = Structure.parse(syntax, model.name, text)

    make_tree(0, structure) foreach (node => data.root.add(node))
  }
}


class Isabelle_Sidekick_Raw extends Isabelle_Sidekick("isabelle-raw")
{
  def parser(data: SideKickParsedData, model: Document_Model)
  {
    val root = data.root
    val snapshot = Swing_Thread.now { model.snapshot() }  // FIXME cover all nodes (!??)
    for ((command, command_start) <- snapshot.node.command_range() if !stopped) {
      snapshot.state.command_state(snapshot.version, command).markup
        .swing_tree(root)((info: Text.Markup) =>
          {
            val range = info.range + command_start
            val content = command.source(info.range).replace('\n', ' ')
            val info_text =
              info.info match {
                case elem @ XML.Elem(_, _) => Pretty.formatted(List(elem), margin = 40).mkString
                case x => x.toString
              }

            new DefaultMutableTreeNode(
              new Isabelle_Sidekick.Asset(command.toString, range.start, range.stop) {
                override def getShortString: String = content
                override def getLongString: String = info_text
                override def toString = quote(content) + " " + range.toString
              })
          })
    }
  }
}

