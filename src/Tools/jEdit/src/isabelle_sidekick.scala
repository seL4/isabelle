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
    new Position { def getOffset = offset; override def toString: String = offset.toString }

  def root_data(buffer: Buffer): SideKickParsedData =
  {
    val data = new SideKickParsedData(buffer.getName)
    data.getAsset(data.root).setEnd(int_to_pos(buffer.getLength))
    data
  }

  class Asset(name: String, start: Text.Offset, end: Text.Offset) extends IAsset
  {
    protected var _name = name
    protected var _start = int_to_pos(start)
    protected var _end = int_to_pos(end)
    override def getIcon: Icon = null
    override def getShortString: String =
      "<html><span style=\"font-family: " + Font_Info.main_family() + ";\">" +
      HTML.encode(_name) + "</span></html>"
    override def getLongString: String = _name
    override def getName: String = _name
    override def setName(name: String) = _name = name
    override def getStart: Position = _start
    override def setStart(start: Position) = _start = start
    override def getEnd: Position = _end
    override def setEnd(end: Position) = _end = end
    override def toString: String = _name
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
    val data = Isabelle_Sidekick.root_data(buffer)
    val syntax = Isabelle.mode_syntax(name)
    val ok =
      if (syntax.isDefined) {
        val ok = parser(buffer, syntax.get, data)
        if (stopped) { data.root.add(new DefaultMutableTreeNode("<stopped>")); true }
        else ok
      }
      else false
    if (!ok) data.root.add(new DefaultMutableTreeNode("<ignored>"))

    data
  }
}


class Isabelle_Sidekick_Structure(
    name: String,
    node_name: Buffer => Option[Document.Node.Name])
  extends Isabelle_Sidekick(name)
{
  override def parser(buffer: Buffer, syntax: Outer_Syntax, data: SideKickParsedData): Boolean =
  {
    def make_tree(offset: Text.Offset, entry: Thy_Structure.Entry): List[DefaultMutableTreeNode] =
      entry match {
        case Thy_Structure.Block(name, body) =>
          val node =
            new DefaultMutableTreeNode(
              new Isabelle_Sidekick.Asset(Library.first_line(name), offset, offset + entry.length))
          (offset /: body)((i, e) =>
            {
              make_tree(i, e) foreach (nd => node.add(nd))
              i + e.length
            })
          List(node)
        case Thy_Structure.Atom(command)
        if command.is_proper && syntax.heading_level(command).isEmpty =>
          val node =
            new DefaultMutableTreeNode(
              new Isabelle_Sidekick.Asset(command.name, offset, offset + entry.length))
          List(node)
        case _ => Nil
      }

    node_name(buffer) match {
      case Some(name) =>
        val text = JEdit_Lib.buffer_text(buffer)
        val structure = Thy_Structure.parse(syntax, name, text)
        make_tree(0, structure) foreach (node => data.root.add(node))
        true
      case None => false
    }
  }
}


class Isabelle_Sidekick_Default extends
  Isabelle_Sidekick_Structure("isabelle", PIDE.resources.theory_node_name)


class Isabelle_Sidekick_Options extends
  Isabelle_Sidekick_Structure("isabelle-options", _ => Some(Document.Node.Name("options")))


class Isabelle_Sidekick_Root extends
  Isabelle_Sidekick_Structure("isabelle-root", _ => Some(Document.Node.Name("ROOT")))


class Isabelle_Sidekick_Markup extends Isabelle_Sidekick("isabelle-markup")
{
  override def parser(buffer: Buffer, syntax: Outer_Syntax, data: SideKickParsedData): Boolean =
  {
    val opt_snapshot =
      GUI_Thread.now {
        Document_Model(buffer) match {
          case Some(model) if model.is_theory => Some(model.snapshot)
          case _ => None
        }
      }
    opt_snapshot match {
      case Some(snapshot) =>
        for ((command, command_start) <- snapshot.node.command_iterator() if !stopped) {
          val markup =
            snapshot.state.command_markup(
              snapshot.version, command, Command.Markup_Index.markup,
                command.range, Markup.Elements.full)
          Isabelle_Sidekick.swing_markup_tree(markup, data.root,
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
                    override def toString: String = quote(content) + " " + range.toString
                  })
              })
        }
        true
      case None => false
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
          data.root.add(make_node(s, offset, offset + line.length))
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


class Isabelle_Sidekick_Bibtex extends SideKickParser("bibtex")
{
  override def supportsCompletion = false

  private class Asset(label: String, start: Text.Offset, stop: Text.Offset) extends
    Isabelle_Sidekick.Asset(label, start, stop) { override def getShortString: String = _name }

  def parse(buffer: Buffer, error_source: errorlist.DefaultErrorSource): SideKickParsedData =
  {
    val data = Isabelle_Sidekick.root_data(buffer)

    try {
      var offset = 0
      for (chunk <- Bibtex.parse(JEdit_Lib.buffer_text(buffer))) {
        val n = chunk.source.size
        chunk match {
          case item: Bibtex.Item if item.is_wellformed =>
            val label = if (item.name == "") item.kind else item.kind + " " + item.name
            val asset = new Isabelle_Sidekick.Asset(label, offset, offset + n)
            data.root.add(new DefaultMutableTreeNode(asset))
          case _ =>
        }
        offset += n
      }
      data
    }
    catch { case ERROR(_) => null }
  }
}

