/*  Title:      Pure/General/markup.scala
    Author:     Makarius

Common markup elements.
*/

package isabelle


object Markup
{
  /* empty */

  val Empty = Markup("", Nil)


  /* misc properties */

  val NAME = "name"
  val Name = new Properties.String(NAME)

  val KIND = "kind"
  val Kind = new Properties.String(KIND)


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
  val OFFSET = "offset"
  val END_OFFSET = "end_offset"
  val FILE = "file"
  val ID = "id"

  val DEF_LINE = "def_line"
  val DEF_OFFSET = "def_offset"
  val DEF_END_OFFSET = "def_end_offset"
  val DEF_FILE = "def_file"
  val DEF_ID = "def_id"

  val POSITION_PROPERTIES = Set(LINE, OFFSET, END_OFFSET, FILE, ID)
  val POSITION = "position"


  /* path */

  val PATH = "path"

  object Path
  {
    def unapply(markup: Markup): Option[String] =
      markup match {
        case Markup(PATH, Name(name)) => Some(name)
        case _ => None
      }
  }


  /* pretty printing */

  val Indent = new Properties.Int("indent")
  val BLOCK = "block"
  val Width = new Properties.Int("width")
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

  val TYPING = "typing"

  val ATTRIBUTE = "attribute"
  val METHOD = "method"


  /* embedded source text */

  val ML_SOURCE = "ML_source"
  val DOC_SOURCE = "doc_source"

  val ANTIQ = "antiq"
  val ML_ANTIQUOTATION = "ML antiquotation"
  val DOCUMENT_ANTIQUOTATION = "document antiquotation"
  val DOCUMENT_ANTIQUOTATION_OPTION = "document antiquotation option"


  /* ML syntax */

  val ML_KEYWORD = "ML_keyword"
  val ML_DELIMITER = "ML_delimiter"
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
  val STRING = "string"
  val ALTSTRING = "altstring"
  val VERBATIM = "verbatim"
  val COMMENT = "comment"
  val CONTROL = "control"
  val MALFORMED = "malformed"

  val COMMAND_SPAN = "command_span"
  val IGNORED_SPAN = "ignored_span"
  val MALFORMED_SPAN = "malformed_span"


  /* theory loader */

  val LOADED_THEORY = "loaded_theory"


  /* timing */

  val TIMING = "timing"
  val ELAPSED = "elapsed"
  val CPU = "cpu"
  val GC = "gc"

  object Timing
  {
    def apply(timing: isabelle.Timing): Markup =
      Markup(TIMING, List(
        (ELAPSED, Properties.Value.Double(timing.elapsed.seconds)),
        (CPU, Properties.Value.Double(timing.cpu.seconds)),
        (GC, Properties.Value.Double(timing.gc.seconds))))
    def unapply(markup: Markup): Option[isabelle.Timing] =
      markup match {
        case Markup(TIMING, List(
          (ELAPSED, Properties.Value.Double(elapsed)),
          (CPU, Properties.Value.Double(cpu)),
          (GC, Properties.Value.Double(gc)))) =>
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
  val ASSIGN = "assign"


  /* prover process */

  val PROVER_COMMAND = "prover_command"
  val PROVER_ARG = "prover_arg"


  /* messages */

  val Serial = new Properties.Long("serial")

  val MESSAGE = "message"

  val INIT = "init"
  val STATUS = "status"
  val REPORT = "report"
  val WRITELN = "writeln"
  val TRACING = "tracing"
  val WARNING = "warning"
  val ERROR = "error"
  val RAW = "raw"
  val SYSTEM = "system"
  val STDOUT = "stdout"
  val STDERR = "stderr"
  val EXIT = "exit"

  val LEGACY = "legacy"

  val NO_REPORT = "no_report"

  val BAD = "bad"

  val READY = "ready"


  /* raw message functions */

  val FUNCTION = "function"
  val Function = new Properties.String(FUNCTION)

  val Assign_Execs: Properties.T = List((FUNCTION, "assign_execs"))
  val Removed_Versions: Properties.T = List((FUNCTION, "removed_versions"))

  val INVOKE_SCALA = "invoke_scala"
  object Invoke_Scala
  {
    def unapply(props: Properties.T): Option[(String, String)] =
      props match {
        case List((FUNCTION, INVOKE_SCALA), (NAME, name), (ID, id)) => Some((name, id))
        case _ => None
      }
  }

  val CANCEL_SCALA = "cancel_scala"
  object Cancel_Scala
  {
    def unapply(props: Properties.T): Option[String] =
      props match {
        case List((FUNCTION, CANCEL_SCALA), (ID, id)) => Some(id)
        case _ => None
      }
  }


  /* system data */

  val Data = Markup("data", Nil)
}

sealed case class Markup(name: String, properties: Properties.T)
