/*  Title:      Tools/jEdit/src/isabelle_sidekick.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

SideKick parsers for Isabelle proof documents.
*/

package isabelle.jedit


import isabelle._

import scala.collection.Set
import scala.collection.immutable.TreeSet

import java.awt.Component
import javax.swing.tree.DefaultMutableTreeNode
import javax.swing.text.Position
import javax.swing.{Icon, DefaultListCellRenderer, ListCellRenderer, JList}

import org.gjt.sp.jedit.{Buffer, EditPane, TextUtilities, View}
import errorlist.DefaultErrorSource
import sidekick.{SideKickParser, SideKickParsedData, SideKickCompletion,
  SideKickCompletionPopup, IAsset}


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


class Isabelle_Sidekick(name: String, get_syntax: => Option[Outer_Syntax])
  extends SideKickParser(name)
{
  /* parsing */

  @volatile protected var stopped = false
  override def stop() = { stopped = true }

  def parser(buffer: Buffer, syntax: Outer_Syntax, data: SideKickParsedData): Boolean = false

  def parse(buffer: Buffer, error_source: DefaultErrorSource): SideKickParsedData =
  {
    stopped = false

    // FIXME lock buffer (!??)
    val data = new SideKickParsedData(buffer.getName)
    val root = data.root
    data.getAsset(root).setEnd(Isabelle_Sidekick.int_to_pos(buffer.getLength))

    val syntax = get_syntax
    val ok =
      if (syntax.isDefined) {
        val ok = parser(buffer, syntax.get, data)
        if (stopped) { root.add(new DefaultMutableTreeNode("<stopped>")); true }
        else ok
      }
      else false
    if (!ok) root.add(new DefaultMutableTreeNode("<ignored>"))

    data
  }


  /* completion */

  override def supportsCompletion = true
  override def canCompleteAnywhere = true

  override def complete(pane: EditPane, caret: Text.Offset): SideKickCompletion =
  {
    Swing_Thread.assert()

    val buffer = pane.getBuffer
    Isabelle.buffer_lock(buffer) {
      get_syntax match {
        case None => null
        case Some(syntax) =>
          val line = buffer.getLineOfOffset(caret)
          val start = buffer.getLineStartOffset(line)
          val text = buffer.getSegment(start, caret - start)

          syntax.completion.complete(text) match {
            case None => null
            case Some((word, cs)) =>
              val ds =
                (if (Isabelle_Encoding.is_active(buffer))
                  cs.map(Symbol.decode(_)).sorted
                 else cs).filter(_ != word)
              if (ds.isEmpty) null
              else
                new SideKickCompletion(pane.getView, word, ds.toArray.asInstanceOf[Array[Object]]) {
                  override def getRenderer() =
                    new ListCellRenderer[Any] {
                      val default_renderer =
                        (new DefaultListCellRenderer).asInstanceOf[ListCellRenderer[Any]]

                      override def getListCellRendererComponent(
                          list: JList[_ <: Any], value: Any, index: Int,
                          selected: Boolean, focus: Boolean): Component =
                      {
                        val renderer: Component =
                          default_renderer.getListCellRendererComponent(
                            list, value, index, selected, focus)
                        renderer.setFont(pane.getTextArea.getPainter.getFont)
                        renderer
                      }
                    }
                }
          }
      }
    }
  }
}


class Isabelle_Sidekick_Structure(
    name: String,
    get_syntax: => Option[Outer_Syntax],
    node_name: Buffer => Option[Document.Node.Name])
  extends Isabelle_Sidekick(name, get_syntax)
{
  import Thy_Syntax.Structure

  override def parser(buffer: Buffer, syntax: Outer_Syntax, data: SideKickParsedData): Boolean =
  {
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

    node_name(buffer) match {
      case Some(name) =>
        val text = Isabelle.buffer_text(buffer)
        val structure = Structure.parse(syntax, name, text)
        make_tree(0, structure) foreach (node => data.root.add(node))
        true
      case None => false
    }
  }
}


class Isabelle_Sidekick_Default extends Isabelle_Sidekick_Structure(
  "isabelle", Isabelle.get_recent_syntax, Isabelle.buffer_node_name)


class Isabelle_Sidekick_Options extends Isabelle_Sidekick_Structure(
  "isabelle-options", Some(Options.options_syntax), Isabelle.buffer_node_dummy)


class Isabelle_Sidekick_Root extends Isabelle_Sidekick_Structure(
  "isabelle-root", Some(Build.root_syntax), Isabelle.buffer_node_dummy)


class Isabelle_Sidekick_Raw
  extends Isabelle_Sidekick("isabelle-raw", Isabelle.get_recent_syntax)
{
  override def parser(buffer: Buffer, syntax: Outer_Syntax, data: SideKickParsedData): Boolean =
  {
    Swing_Thread.now { Document_Model(buffer).map(_.snapshot) } match {
      case Some(snapshot) =>
        val root = data.root
        for ((command, command_start) <- snapshot.node.command_range() if !stopped) {
          snapshot.state.command_state(snapshot.version, command).markup
            .swing_tree(root)((info: Text.Info[List[XML.Elem]]) =>
              {
                val range = info.range + command_start
                val content = command.source(info.range).replace('\n', ' ')
                val info_text =
                  Pretty.formatted(Library.separate(Pretty.FBreak, info.info), margin = 40).mkString

                new DefaultMutableTreeNode(
                  new Isabelle_Sidekick.Asset(command.toString, range.start, range.stop) {
                    override def getShortString: String = content
                    override def getLongString: String = info_text
                    override def toString = quote(content) + " " + range.toString
                  })
              })
        }
        true
      case None => false
    }
  }
}

