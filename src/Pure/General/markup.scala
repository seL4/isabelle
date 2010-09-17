/*  Title:      Pure/General/markup.scala
    Author:     Makarius

Common markup elements.
*/

package isabelle


object Markup
{
  /* plain values */

  object Int {
    def apply(i: scala.Int): String = i.toString
    def unapply(s: String): Option[scala.Int] =
      try { Some(Integer.parseInt(s)) }
      catch { case _: NumberFormatException => None }
  }

  object Long {
    def apply(i: scala.Long): String = i.toString
    def unapply(s: String): Option[scala.Long] =
      try { Some(java.lang.Long.parseLong(s)) }
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


  /* empty */

  val Empty = Markup("", Nil)


  /* misc properties */

  val NAME = "name"
  val KIND = "kind"


  /* formal entities */

  val BINDING = "binding"
  val ENTITY = "entity"
  val DEF = "def"
  val REF = "ref"


  /* position */

  val LINE = "line"
  val COLUMN = "column"
  val OFFSET = "offset"
  val END_LINE = "end_line"
  val END_COLUMN = "end_column"
  val END_OFFSET = "end_offset"
  val FILE = "file"
  val ID = "id"

  val POSITION_PROPERTIES =
    Set(LINE, COLUMN, OFFSET, END_LINE, END_COLUMN, END_OFFSET, FILE, ID)

  val POSITION = "position"


  /* pretty printing */

  val Indent = new Int_Property("indent")
  val BLOCK = "block"
  val Width = new Int_Property("width")
  val BREAK = "break"


  /* hidden text */

  val HIDDEN = "hidden"


  /* logical entities */

  val TCLASS = "tclass"
  val TYCON = "tycon"
  val FIXED_DECL = "fixed_decl"
  val FIXED = "fixed"
  val CONST_DECL = "const_decl"
  val CONST = "const"
  val FACT_DECL = "fact_decl"
  val FACT = "fact"
  val DYNAMIC_FACT = "dynamic_fact"
  val LOCAL_FACT_DECL = "local_fact_decl"
  val LOCAL_FACT = "local_fact"


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
  val ML_ANTIQ = "ML_antiq"
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
  val ML_REF = "ML_ref"
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

  val PID = "pid"
  val Serial = new Long_Property("serial")

  val MESSAGE = "message"
  val CLASS = "class"

  val INIT = "init"
  val STATUS = "status"
  val WRITELN = "writeln"
  val TRACING = "tracing"
  val WARNING = "warning"
  val ERROR = "error"
  val SYSTEM = "system"
  val INPUT = "input"
  val STDIN = "stdin"
  val STDOUT = "stdout"
  val SIGNAL = "signal"
  val EXIT = "exit"

  val REPORT = "report"
  val NO_REPORT = "no_report"

  val BAD = "bad"

  val Ready = Markup("ready", Nil)


  /* system data */

  val Data = Markup("data", Nil)
}

sealed case class Markup(name: String, properties: List[(String, String)])
