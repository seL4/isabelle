/*  Title:      Tools/jEdit/src/isabelle_sidekick.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

SideKick parsers for Isabelle proof documents.
*/

package isabelle.jedit


import isabelle._

import javax.swing.tree.DefaultMutableTreeNode
import javax.swing.text.Position
import javax.swing.Icon

import org.gjt.sp.jedit.Buffer
import sidekick.{SideKickParser, SideKickParsedData, IAsset}


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
    override def getShortString: String =
      "<html><span style=\"font-family: " + Rendering.font_family() + ";\">" +
      HTML.encode(_name) + "</span></html>"
    override def getLongString: String = _name
    override def getName: String = _name
    override def setName(name: String) = _name = name
    override def getStart: Position = _start
    override def setStart(start: Position) = _start = start
    override def getEnd: Position = _end
    override def setEnd(end: Position) = _end = end
    override def toString = _name
  }

  def swing_markup_tree(tree: Markup_Tree, parent: DefaultMutableTreeNode,
    swing_node: Text.Info[List[XML.Elem]] => DefaultMutableTreeNode)
  {
    for ((_, entry) <- tree.branches) {
      val node = swing_node(Text.Info(entry.range, entry.markup))
      swing_markup_tree(entry.subtree, node, swing_node)
      parent.add(node)
    }
  }
}


class Isabelle_Sidekick(name: String) extends SideKickParser(name)
{
  override def supportsCompletion = false


  /* parsing */

  @volatile protected var stopped = false
  override def stop() = { stopped = true }

  def parser(buffer: Buffer, syntax: Outer_Syntax, data: SideKickParsedData): Boolean = false

  def parse(buffer: Buffer, error_source: errorlist.DefaultErrorSource): SideKickParsedData =
  {
    stopped = false

    // FIXME lock buffer (!??)
    val data = new SideKickParsedData(buffer.getName)
    val root = data.root
    data.getAsset(root).setEnd(Isabelle_Sidekick.int_to_pos(buffer.getLength))

    val syntax = Isabelle.mode_syntax(name)
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
}


class Isabelle_Sidekick_Structure(
    name: String,
    node_name: Buffer => Option[Document.Node.Name])
  extends Isabelle_Sidekick(name)
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
        val text = JEdit_Lib.buffer_text(buffer)
        val structure = Structure.parse(syntax, name, text)
        make_tree(0, structure) foreach (node => data.root.add(node))
        true
      case None => false
    }
  }
}


class Isabelle_Sidekick_Default extends
  Isabelle_Sidekick_Structure("isabelle", PIDE.thy_load.theory_node_name)


class Isabelle_Sidekick_Options extends
  Isabelle_Sidekick_Structure("isabelle-options", _ => Some(Document.Node.Name("options")))


class Isabelle_Sidekick_Root extends
  Isabelle_Sidekick_Structure("isabelle-root", _ => Some(Document.Node.Name("ROOT")))


class Isabelle_Sidekick_Markup extends Isabelle_Sidekick("isabelle-markup")
{
  override def parser(buffer: Buffer, syntax: Outer_Syntax, data: SideKickParsedData): Boolean =
  {
    Swing_Thread.now { Document_Model(buffer) } match {
      case Some(model) if model.is_theory =>
        val snapshot = model.snapshot
        val root = data.root
        for ((command, command_start) <- snapshot.node.command_range() if !stopped) {
          Isabelle_Sidekick.swing_markup_tree(
            snapshot.state.command_state(snapshot.version, command).markup, root,
              (info: Text.Info[List[XML.Elem]]) =>
              {
                val range = info.range + command_start
                val content = command.source(info.range).replace('\n', ' ')
                val info_text =
                  Pretty.formatted(Library.separate(Pretty.FBreak, info.info), margin = 40.0)
                    .mkString

                new DefaultMutableTreeNode(
                  new Isabelle_Sidekick.Asset(command.toString, range.start, range.stop) {
                    override def getShortString: String = content
                    override def getLongString: String = info_text
                    override def toString = quote(content) + " " + range.toString
                  })
              })
        }
        true
      case _ => false
    }
  }
}


class Isabelle_Sidekick_News extends Isabelle_Sidekick("isabelle-news")
{
  private val Heading1 = """^New in (.*)\w*$""".r
  private val Heading2 = """^\*\*\*\w*(.*)\w*\*\*\*\w*$""".r

  private def make_node(s: String, start: Text.Offset, stop: Text.Offset): DefaultMutableTreeNode =
    new DefaultMutableTreeNode(new Isabelle_Sidekick.Asset(s, start, stop))

  override def parser(buffer: Buffer, syntax: Outer_Syntax, data: SideKickParsedData): Boolean =
  {
    var offset = 0

    for (line <- split_lines(JEdit_Lib.buffer_text(buffer)) if !stopped) {
      line match {
        case Heading1(s) =>
          data.root.add(make_node(Library.capitalize(s), offset, offset + line.length))
        case Heading2(s) =>
          data.root.getLastChild.asInstanceOf[DefaultMutableTreeNode]
            .add(make_node(s, offset, offset + line.length))
        case _ =>
      }
      offset += line.length + 1
    }

    true
  }
}

