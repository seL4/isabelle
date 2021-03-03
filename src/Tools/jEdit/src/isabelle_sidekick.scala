/*  Title:      Tools/jEdit/src/isabelle_sidekick.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

SideKick parsers for Isabelle proof documents.
*/

package isabelle.jedit


import isabelle._

import javax.swing.tree.DefaultMutableTreeNode
import javax.swing.text.Position
import javax.swing.{JLabel, Icon}

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

  class Keyword_Asset(keyword: String, text: String, range: Text.Range) extends IAsset
  {
    private val css = GUI.imitate_font_css(GUI.label_font())

    protected var _name = text
    protected var _start = int_to_pos(range.start)
    protected var _end = int_to_pos(range.stop)
    override def getIcon: Icon = null
    override def getShortString: String =
    {
      val n = keyword.length
      val s =
        _name.indexOf(keyword) match {
          case i if i >= 0 && n > 0 =>
            HTML.output(_name.substring(0, i)) +
            "<b>" + HTML.output(keyword) + "</b>" +
            HTML.output(_name.substring(i + n))
          case _ => HTML.output(_name)
        }
      "<html><span style=\"" + css + "\">" + s + "</span></html>"
    }
    override def getLongString: String = _name
    override def getName: String = _name
    override def setName(name: String): Unit = _name = name
    override def getStart: Position = _start
    override def setStart(start: Position): Unit = _start = start
    override def getEnd: Position = _end
    override def setEnd(end: Position): Unit = _end = end
    override def toString: String = _name
  }

  class Asset(name: String, range: Text.Range) extends Keyword_Asset("", name, range)

  def swing_markup_tree(tree: Markup_Tree, parent: DefaultMutableTreeNode,
    swing_node: Text.Info[List[XML.Elem]] => DefaultMutableTreeNode): Unit =
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
    val syntax = Isabelle.buffer_syntax(buffer)
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
    node_name: Buffer => Option[Document.Node.Name],
    parse: (Outer_Syntax, Document.Node.Name, CharSequence) => List[Document_Structure.Document])
  extends Isabelle_Sidekick(name)
{
  override def parser(buffer: Buffer, syntax: Outer_Syntax, data: SideKickParsedData): Boolean =
  {
    def make_tree(
      parent: DefaultMutableTreeNode,
      offset: Text.Offset,
      documents: List[Document_Structure.Document]): Unit =
    {
      documents.foldLeft(offset) { case (i, document) =>
        document match {
          case Document_Structure.Block(name, text, body) =>
            val range = Text.Range(i, i + document.length)
            val node =
              new DefaultMutableTreeNode(
                new Isabelle_Sidekick.Keyword_Asset(name, Library.first_line(text), range))
            parent.add(node)
            make_tree(node, i, body)
          case _ =>
        }
        i + document.length
      }
    }

    node_name(buffer) match {
      case Some(name) =>
        make_tree(data.root, 0, parse(syntax, name, JEdit_Lib.buffer_text(buffer)))
        true
      case None =>
        false
    }
  }
}

class Isabelle_Sidekick_Default extends
  Isabelle_Sidekick_Structure("isabelle",
    PIDE.resources.theory_node_name, Document_Structure.parse_sections)

class Isabelle_Sidekick_Context extends
  Isabelle_Sidekick_Structure("isabelle-context",
    PIDE.resources.theory_node_name, Document_Structure.parse_blocks)

class Isabelle_Sidekick_Options extends
  Isabelle_Sidekick_Structure("isabelle-options",
    _ => Some(Document.Node.Name("options")), Document_Structure.parse_sections)

class Isabelle_Sidekick_Root extends
  Isabelle_Sidekick_Structure("isabelle-root",
    _ => Some(Document.Node.Name("ROOT")), Document_Structure.parse_sections)

class Isabelle_Sidekick_ML extends
  Isabelle_Sidekick_Structure("isabelle-ml",
    buffer => Some(PIDE.resources.node_name(buffer)),
    (_, _, text) => Document_Structure.parse_ml_sections(false, text))

class Isabelle_Sidekick_SML extends
  Isabelle_Sidekick_Structure("isabelle-sml",
    buffer => Some(PIDE.resources.node_name(buffer)),
    (_, _, text) => Document_Structure.parse_ml_sections(true, text))


class Isabelle_Sidekick_Markup extends Isabelle_Sidekick("isabelle-markup")
{
  override def parser(buffer: Buffer, syntax: Outer_Syntax, data: SideKickParsedData): Boolean =
  {
    val opt_snapshot =
      Document_Model.get(buffer) match {
        case Some(model) if model.is_theory => Some(model.snapshot)
        case _ => None
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
                val info_text = Pretty.formatted(Pretty.fbreaks(info.info), margin = 40.0).mkString

                new DefaultMutableTreeNode(
                  new Isabelle_Sidekick.Asset(command.toString, range) {
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
    new DefaultMutableTreeNode(new Isabelle_Sidekick.Asset(s, Text.Range(start, stop)))

  override def parser(buffer: Buffer, syntax: Outer_Syntax, data: SideKickParsedData): Boolean =
  {
    var offset = 0
    var end_offset = 0

    var start1: Option[(Int, String, Vector[DefaultMutableTreeNode])] = None
    var start2: Option[(Int, String)] = None

    def close1: Unit =
      start1 match {
        case Some((start_offset, s, body)) =>
          val node = make_node(s, start_offset, end_offset)
          body.foreach(node.add(_))
          data.root.add(node)
          start1 = None
        case None =>
      }

    def close2: Unit =
      start2 match {
        case Some((start_offset, s)) =>
          start1 match {
            case Some((start_offset1, s1, body)) =>
              val node = make_node(s, start_offset, end_offset)
              start1 = Some((start_offset1, s1, body :+ node))
            case None =>
          }
          start2 = None
        case None =>
      }

    for (line <- split_lines(JEdit_Lib.buffer_text(buffer)) if !stopped) {
      line match {
        case Heading1(s) => close2; close1; start1 = Some((offset, s, Vector()))
        case Heading2(s) => close2; start2 = Some((offset, s))
        case _ =>
      }
      offset += line.length + 1
      if (!line.forall(Character.isSpaceChar)) end_offset = offset
    }
    if (!stopped) { close2; close1 }

    true
  }
}

