/*  Title:      Pure/General/markup.scala
    Author:     Makarius

Common markup elements.
*/

package isabelle


object Markup
{
  /* name */

  val NAME = "name"
  val KIND = "kind"


  /* formal entities */

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
  val LOCATION = "location"


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

  val STATE = "state"
  val SUBGOAL = "subgoal"
  val SENDBACK = "sendback"
  val HILITE = "hilite"


  /* command status */

  val TASK = "task"

  val UNPROCESSED = "unprocessed"
  val RUNNING = "running"
  val FAILED = "failed"
  val FINISHED = "finished"
  val DISPOSED = "disposed"


  /* interactive documents */

  val EDITS = "edits"
  val EDIT = "edit"


  /* messages */

  val PID = "pid"
  val SESSION = "session"

  val MESSAGE = "message"
  val CLASS = "class"

  val INIT = "init"
  val STATUS = "status"
  val WRITELN = "writeln"
  val PRIORITY = "priority"
  val TRACING = "tracing"
  val WARNING = "warning"
  val ERROR = "error"
  val DEBUG = "debug"
  val SYSTEM = "system"
  val STDIN = "stdin"
  val STDOUT = "stdout"
  val SIGNAL = "signal"
  val EXIT = "exit"

  val READY = "ready"


  /* content */

  val ROOT = "root"
  val RAW = "raw"
  val BAD = "bad"
}
