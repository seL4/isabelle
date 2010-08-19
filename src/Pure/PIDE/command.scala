/*  Title:      Pure/PIDE/command.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Prover commands with semantic state.
*/

package isabelle


import scala.actors.Actor, Actor._
import scala.collection.mutable


object Command
{
  case class HighlightInfo(kind: String, sub_kind: Option[String]) {
    override def toString = kind
  }
  case class TypeInfo(ty: String)
  case class RefInfo(file: Option[String], line: Option[Int],
    command_id: Option[Document.Command_ID], offset: Option[Int])  // FIXME Command_ID vs. Exec_ID !?



  /** accumulated results from prover **/

  case class State(
    val command: Command,
    val status: List[XML.Tree],
    val reverse_results: List[XML.Tree],
    val markup: Markup_Tree)
  {
    /* content */

    lazy val results = reverse_results.reverse

    def add_result(result: XML.Tree): State = copy(reverse_results = result :: reverse_results)

    def add_markup(node: Markup_Tree.Node[Any]): State = copy(markup = markup + node)

    def markup_root_node: Markup_Tree.Node[Any] =
      new Markup_Tree.Node(command.range, XML.Elem(Markup(Markup.STATUS, Nil), status))
    def markup_root: Markup_Tree = markup + markup_root_node


    /* markup */

    lazy val highlight: List[Markup_Tree.Node[Any]] =
    {
      markup.filter(_.info match {
        case Command.HighlightInfo(_, _) => true
        case _ => false
      }).flatten(markup_root_node)
    }

    private lazy val types: List[Markup_Tree.Node[Any]] =
      markup.filter(_.info match {
        case Command.TypeInfo(_) => true
        case _ => false }).flatten(markup_root_node)

    def type_at(pos: Text.Offset): Option[String] =
    {
      types.find(_.range.contains(pos)) match {
        case Some(t) =>
          t.info match {
            case Command.TypeInfo(ty) => Some(command.source(t.range) + " : " + ty)
            case _ => None
          }
        case None => None
      }
    }

    private lazy val refs: List[Markup_Tree.Node[Any]] =
      markup.filter(_.info match {
        case Command.RefInfo(_, _, _, _) => true
        case _ => false }).flatten(markup_root_node)

    def ref_at(pos: Text.Offset): Option[Markup_Tree.Node[Any]] =
      refs.find(_.range.contains(pos))


    /* message dispatch */

    def accumulate(message: XML.Tree): Command.State =
      message match {
        case XML.Elem(Markup(Markup.STATUS, _), body) => copy(status = body ::: status)

        case XML.Elem(Markup(Markup.REPORT, _), elems) =>
          (this /: elems)((state, elem) =>
            elem match {
              case XML.Elem(Markup(kind, atts), body) if Position.get_id(atts) == Some(command.id) =>
                atts match {
                  case Position.Range(range) =>
                    if (kind == Markup.ML_TYPING) {
                      val info = Pretty.string_of(body, margin = 40)
                      state.add_markup(command.decode_range(range, Command.TypeInfo(info)))
                    }
                    else if (kind == Markup.ML_REF) {
                      body match {
                        case List(XML.Elem(Markup(Markup.ML_DEF, props), _)) =>
                          state.add_markup(
                            command.decode_range(range,
                              Command.RefInfo(
                                Position.get_file(props),
                                Position.get_line(props),
                                Position.get_id(props),
                                Position.get_offset(props))))
                        case _ => state
                      }
                    }
                    else {
                      state.add_markup(
                        command.decode_range(range,
                          Command.HighlightInfo(kind, Markup.get_string(Markup.KIND, atts))))
                    }
                  case _ => state
                }
              case _ => System.err.println("Ignored report message: " + elem); state
            })
        case _ => add_result(message)
      }
  }


  /* unparsed dummy commands */

  def unparsed(source: String) =
    new Command(Document.NO_ID, List(Token(Token.Kind.UNPARSED, source)))
}


class Command(
    val id: Document.Command_ID,
    val span: List[Token])
{
  /* classification */

  def is_command: Boolean = !span.isEmpty && span.head.is_command
  def is_ignored: Boolean = span.forall(_.is_ignored)
  def is_malformed: Boolean = !is_command && !is_ignored

  def is_unparsed = id == Document.NO_ID

  def name: String = if (is_command) span.head.content else ""
  override def toString =
    id + "/" + (if (is_command) name else if (is_ignored) "IGNORED" else "MALFORMED")


  /* source text */

  val source: String = span.map(_.source).mkString
  def source(range: Text.Range): String = source.substring(range.start, range.stop)
  def length: Int = source.length
  val range: Text.Range = Text.Range(0, length)

  lazy val symbol_index = new Symbol.Index(source)


  /* markup */

  def decode_range(range: Text.Range, info: Any): Markup_Tree.Node[Any] =
    new Markup_Tree.Node(symbol_index.decode(range), info)


  /* accumulated results */

  val empty_state: Command.State = Command.State(this, Nil, Nil, Markup_Tree.empty)
}
