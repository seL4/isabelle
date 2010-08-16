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
  object Status extends Enumeration
  {
    val UNPROCESSED = Value("UNPROCESSED")
    val FINISHED = Value("FINISHED")
    val FAILED = Value("FAILED")
    val UNDEFINED = Value("UNDEFINED")
  }

  case class HighlightInfo(kind: String, sub_kind: Option[String]) {
    override def toString = kind
  }
  case class TypeInfo(ty: String)
  case class RefInfo(file: Option[String], line: Option[Int],
    command_id: Option[Document.Command_ID], offset: Option[Int])  // FIXME Command_ID vs. Exec_ID !?



  /** accumulated results from prover **/

  case class State(
    val command: Command,
    val status: Command.Status.Value,
    val forks: Int,
    val reverse_results: List[XML.Tree],
    val markup: Markup_Text)
  {
    /* content */

    lazy val results = reverse_results.reverse

    def add_result(result: XML.Tree): State = copy(reverse_results = result :: reverse_results)

    def add_markup(node: Markup_Tree): State = copy(markup = markup + node)


    /* markup */

    lazy val highlight: Markup_Text =
    {
      markup.filter(_.info match {
        case Command.HighlightInfo(_, _) => true
        case _ => false
      })
    }

    private lazy val types: List[Markup_Node] =
      markup.filter(_.info match {
        case Command.TypeInfo(_) => true
        case _ => false }).flatten

    def type_at(pos: Int): Option[String] =
    {
      types.find(t => t.start <= pos && pos < t.stop) match {
        case Some(t) =>
          t.info match {
            case Command.TypeInfo(ty) => Some(command.source(t.start, t.stop) + " : " + ty)
            case _ => None
          }
        case None => None
      }
    }

    private lazy val refs: List[Markup_Node] =
      markup.filter(_.info match {
        case Command.RefInfo(_, _, _, _) => true
        case _ => false }).flatten

    def ref_at(pos: Int): Option[Markup_Node] =
      refs.find(t => t.start <= pos && pos < t.stop)


    /* message dispatch */

    def accumulate(message: XML.Tree): Command.State =
      message match {
        case XML.Elem(Markup(Markup.STATUS, _), elems) =>
          (this /: elems)((state, elem) =>
            elem match {
              case XML.Elem(Markup(Markup.UNPROCESSED, _), _) => state.copy(status = Command.Status.UNPROCESSED)
              case XML.Elem(Markup(Markup.FINISHED, _), _) => state.copy(status = Command.Status.FINISHED)
              case XML.Elem(Markup(Markup.FAILED, _), _) => state.copy(status = Command.Status.FAILED)
              case XML.Elem(Markup(Markup.FORKED, _), _) => state.copy(forks = state.forks + 1)
              case XML.Elem(Markup(Markup.JOINED, _), _) => state.copy(forks = state.forks - 1)
              case _ => System.err.println("Ignored status message: " + elem); state
            })

        case XML.Elem(Markup(Markup.REPORT, _), elems) =>
          (this /: elems)((state, elem) =>
            elem match {
              case XML.Elem(Markup(kind, atts), body) if Position.get_id(atts) == Some(command.id) =>
                atts match {
                  case Position.Range(begin, end) =>
                    if (kind == Markup.ML_TYPING) {
                      val info = Pretty.string_of(body, margin = 40)
                      state.add_markup(
                        command.markup_node(begin - 1, end - 1, Command.TypeInfo(info)))
                    }
                    else if (kind == Markup.ML_REF) {
                      body match {
                        case List(XML.Elem(Markup(Markup.ML_DEF, props), _)) =>
                          state.add_markup(
                            command.markup_node(
                              begin - 1, end - 1,
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
                        command.markup_node(begin - 1, end - 1,
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
  def source(i: Int, j: Int): String = source.substring(i, j)
  def length: Int = source.length

  lazy val symbol_index = new Symbol.Index(source)


  /* markup */

  def markup_node(begin: Int, end: Int, info: Any): Markup_Tree =
  {
    val start = symbol_index.decode(begin)
    val stop = symbol_index.decode(end)
    new Markup_Tree(new Markup_Node(start, stop, info), Nil)
  }


  /* accumulated results */

  val empty_state: Command.State =
    Command.State(this, Command.Status.UNPROCESSED, 0, Nil, new Markup_Text(Nil, source))
}
