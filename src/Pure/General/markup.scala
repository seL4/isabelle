/*  Title:      Pure/General/markup.scala
    Author:     Makarius

Common markup elements.
*/

package isabelle


object Markup
{
  /* plain values */

  object Int
  {
    def apply(x: scala.Int): String = x.toString
    def unapply(s: String): Option[scala.Int] =
      try { Some(Integer.parseInt(s)) }
      catch { case _: NumberFormatException => None }
  }

  object Long
  {
    def apply(x: scala.Long): String = x.toString
    def unapply(s: String): Option[scala.Long] =
      try { Some(java.lang.Long.parseLong(s)) }
      catch { case _: NumberFormatException => None }
  }

  object Double
  {
    def apply(x: scala.Double): String = x.toString
    def unapply(s: String): Option[scala.Double] =
      try { Some(java.lang.Double.parseDouble(s)) }
      catch { case _: NumberFormatException => None }
  }


  /* named properties */

  class Property(val name: String)
  {
    def apply(value: String): List[(String, String)] = List((name, value))
    def unapply(props: List[(String, String)]): Option[String] =
      props.find(_._1 == name).map(_._2)
  }

  class Int_Property(name: String)
  {
    def apply(value: scala.Int): List[(String, String)] = List((name, Int(value)))
    def unapply(props: List[(String, String)]): Option[Int] =
      props.find(_._1 == name) match {
        case None => None
        case Some((_, value)) => Int.unapply(value)
      }
  }

  class Long_Property(name: String)
  {
    def apply(value: scala.Long): List[(String, String)] = List((name, Long(value)))
    def unapply(props: List[(String, String)]): Option[Long] =
      props.find(_._1 == name) match {
        case None => None
        case Some((_, value)) => Long.unapply(value)
      }
  }

  class Double_Property(name: String)
  {
    def apply(value: scala.Double): List[(String, String)] = List((name, Double(value)))
    def unapply(props: List[(String, String)]): Option[Double] =
      props.find(_._1 == name) match {
        case None => None
        case Some((_, value)) => Double.unapply(value)
      }
  }


  /* empty */

  val Empty = Markup("", Nil)


  /* misc properties */

  val NAME = "name"
  val Name = new Property(NAME)

  val KIND = "kind"
  val Kind = new Property(KIND)


  /* formal entities */

  val BINDING = "binding"
  val ENTITY = "entity"
  val DEF = "def"
  val REF = "ref"

  object Entity
  {
    def unapply(markup: Markup): Option[(String, String)] =
      markup match {
        case Markup(ENTITY, props @ Kind(kind)) =>
          props match {
            case Name(name) => Some(kind, name)
            case _ => None
          }
        case _ => None
      }
  }


  /* position */

  val LINE = "line"
  val COLUMN = "column"
  val OFFSET = "offset"
  val END_OFFSET = "end_offset"
  val FILE = "file"
  val ID = "id"

  val DEF_LINE = "def_line"
  val DEF_COLUMN = "def_column"
  val DEF_OFFSET = "def_offset"
  val DEF_END_OFFSET = "def_end_offset"
  val DEF_FILE = "def_file"
  val DEF_ID = "def_id"

  val POSITION_PROPERTIES = Set(LINE, COLUMN, OFFSET, END_OFFSET, FILE, ID)

  val POSITION = "position"


  /* pretty printing */

  val Indent = new Int_Property("indent")
  val BLOCK = "block"
  val Width = new Int_Property("width")
  val BREAK = "break"


  /* hidden text */

  val HIDDEN = "hidden"


  /* logical entities */

  val CLASS = "class"
  val TYPE = "type"
  val FIXED = "fixed"
  val CONSTANT = "constant"

  val DYNAMIC_FACT = "dynamic_fact"


  /* inner syntax */

  val TFREE = "tfree"
  val TVAR = "tvar"
  val FREE = "free"
  val SKOLEM = "skolem"
  val BOUND = "bound"
  val VAR = "var"
  val NUM = "num"
  val FLOAT = "float"
  val XNUM = "xnum"
  val XSTR = "xstr"
  val LITERAL = "literal"
  val DELIMITER = "delimiter"
  val INNER_STRING = "inner_string"
  val INNER_COMMENT = "inner_comment"

  val TOKEN_RANGE = "token_range"

  val SORT = "sort"
  val TYP = "typ"
  val TERM = "term"
  val PROP = "prop"

  val ATTRIBUTE = "attribute"
  val METHOD = "method"


  /* embedded source text */

  val ML_SOURCE = "ML_source"
  val DOC_SOURCE = "doc_source"

  val ANTIQ = "antiq"
  val ML_ANTIQUOTATION = "ML antiquotation"
  val DOC_ANTIQ = "doc_antiq"


  /* ML syntax */

  val ML_KEYWORD = "ML_keyword"
  val ML_DELIMITER = "ML_delimiter"
  val ML_IDENT = "ML_ident"
  val ML_TVAR = "ML_tvar"
  val ML_NUMERAL = "ML_numeral"
  val ML_CHAR = "ML_char"
  val ML_STRING = "ML_string"
  val ML_COMMENT = "ML_comment"
  val ML_MALFORMED = "ML_malformed"

  val ML_DEF = "ML_def"
  val ML_OPEN = "ML_open"
  val ML_STRUCT = "ML_struct"
  val ML_TYPING = "ML_typing"


  /* outer syntax */

  val KEYWORD_DECL = "keyword_decl"
  val COMMAND_DECL = "command_decl"

  val KEYWORD = "keyword"
  val OPERATOR = "operator"
  val COMMAND = "command"
  val IDENT = "ident"
  val STRING = "string"
  val ALTSTRING = "altstring"
  val VERBATIM = "verbatim"
  val COMMENT = "comment"
  val CONTROL = "control"
  val MALFORMED = "malformed"

  val COMMAND_SPAN = "command_span"
  val IGNORED_SPAN = "ignored_span"
  val MALFORMED_SPAN = "malformed_span"


  /* timing */

  val TIMING = "timing"
  val ELAPSED = "elapsed"
  val CPU = "cpu"
  val GC = "gc"

  object Timing
  {
    def apply(timing: isabelle.Timing): Markup =
      Markup(TIMING, List(
        (ELAPSED, Double(timing.elapsed.seconds)),
        (CPU, Double(timing.cpu.seconds)),
        (GC, Double(timing.gc.seconds))))
    def unapply(markup: Markup): Option[isabelle.Timing] =
      markup match {
        case Markup(TIMING, List(
          (ELAPSED, Double(elapsed)), (CPU, Double(cpu)), (GC, Double(gc)))) =>
            Some(new isabelle.Timing(Time.seconds(elapsed), Time.seconds(cpu), Time.seconds(gc)))
        case _ => None
      }
  }


  /* toplevel */

  val SUBGOALS = "subgoals"
  val PROOF_STATE = "proof_state"

  val STATE = "state"
  val SUBGOAL = "subgoal"
  val SENDBACK = "sendback"
  val HILITE = "hilite"


  /* command status */

  val TASK = "task"

  val FORKED = "forked"
  val JOINED = "joined"
  val FAILED = "failed"
  val FINISHED = "finished"


  /* interactive documents */

  val VERSION = "version"
  val EXEC = "exec"
  val ASSIGN = "assign"
  val EDIT = "edit"


  /* messages */

  val Serial = new Long_Property("serial")

  val MESSAGE = "message"

  val INIT = "init"
  val STATUS = "status"
  val REPORT = "report"
  val WRITELN = "writeln"
  val TRACING = "tracing"
  val WARNING = "warning"
  val ERROR = "error"
  val SYSTEM = "system"
  val STDOUT = "stdout"
  val EXIT = "exit"

  val NO_REPORT = "no_report"

  val BAD = "bad"

  val READY = "ready"


  /* system data */

  val Data = Markup("data", Nil)
}

sealed case class Markup(name: String, properties: List[(String, String)])
