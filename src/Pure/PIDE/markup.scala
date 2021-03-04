/*  Title:      Pure/PIDE/markup.scala
    Author:     Makarius

Quasi-abstract markup elements.
*/

package isabelle


object Markup
{
  /* elements */

  object Elements
  {
    def apply(elems: Set[String]): Elements = new Elements(elems)
    def apply(elems: String*): Elements = apply(Set(elems: _*))
    val empty: Elements = apply()
    val full: Elements =
      new Elements(Set.empty)
      {
        override def apply(elem: String): Boolean = true
        override def toString: String = "Elements.full"
      }
  }

  sealed class Elements private[Markup](private val rep: Set[String])
  {
    def apply(elem: String): Boolean = rep.contains(elem)
    def + (elem: String): Elements = new Elements(rep + elem)
    def ++ (elems: Elements): Elements = new Elements(rep ++ elems.rep)
    def - (elem: String): Elements = new Elements(rep - elem)
    def -- (elems: Elements): Elements = new Elements(rep -- elems.rep)
    override def toString: String = rep.mkString("Elements(", ",", ")")
  }


  /* properties */

  val NAME = "name"
  val Name = new Properties.String(NAME)

  val XNAME = "xname"
  val XName = new Properties.String(XNAME)

  val KIND = "kind"
  val Kind = new Properties.String(KIND)

  val CONTENT = "content"
  val Content = new Properties.String(CONTENT)

  val SERIAL = "serial"
  val Serial = new Properties.Long(SERIAL)

  val INSTANCE = "instance"
  val Instance = new Properties.String(INSTANCE)


  /* basic markup */

  val Empty: Markup = Markup("", Nil)
  val Broken: Markup = Markup("broken", Nil)

  class Markup_String(val name: String, prop: String)
  {
    private val Prop = new Properties.String(prop)

    def apply(s: String): Markup = Markup(name, Prop(s))
    def unapply(markup: Markup): Option[String] =
      if (markup.name == name) Prop.unapply(markup.properties) else None
  }

  class Markup_Int(val name: String, prop: String)
  {
    private val Prop = new Properties.Int(prop)

    def apply(i: Int): Markup = Markup(name, Prop(i))
    def unapply(markup: Markup): Option[Int] =
      if (markup.name == name) Prop.unapply(markup.properties) else None
  }

  class Markup_Long(val name: String, prop: String)
  {
    private val Prop = new Properties.Long(prop)

    def apply(i: Long): Markup = Markup(name, Prop(i))
    def unapply(markup: Markup): Option[Long] =
      if (markup.name == name) Prop.unapply(markup.properties) else None
  }


  /* meta data */

  val META_TITLE = "meta_title"
  val META_CREATOR = "meta_creator"
  val META_CONTRIBUTOR = "meta_contributor"
  val META_DATE = "meta_date"
  val META_LICENSE = "meta_license"
  val META_DESCRIPTION = "meta_description"


  /* formal entities */

  val BINDING = "binding"
  val ENTITY = "entity"

  val Def = new Properties.Long("def")
  val Ref = new Properties.Long("ref")

  object Entity
  {
    object Def
    {
      def unapply(markup: Markup): Option[Long] =
        if (markup.name == ENTITY) Markup.Def.unapply(markup.properties) else None
    }
    object Ref
    {
      def unapply(markup: Markup): Option[Long] =
        if (markup.name == ENTITY) Markup.Ref.unapply(markup.properties) else None
    }
    object Occ
    {
      def unapply(markup: Markup): Option[Long] =
        Def.unapply(markup) orElse Ref.unapply(markup)
    }

    def unapply(markup: Markup): Option[(String, String)] =
      markup match {
        case Markup(ENTITY, props) =>
          val kind = Kind.unapply(props).getOrElse("")
          val name = Name.unapply(props).getOrElse("")
          Some((kind, name))
        case _ => None
      }
  }


  /* completion */

  val COMPLETION = "completion"
  val NO_COMPLETION = "no_completion"

  val UPDATE = "update"


  /* position */

  val LINE = "line"
  val END_LINE = "line"
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
  def position_property(entry: Properties.Entry): Boolean = POSITION_PROPERTIES(entry._1)

  val POSITION = "position"


  /* expression */

  val EXPRESSION = "expression"
  object Expression
  {
    def unapply(markup: Markup): Option[String] =
      markup match {
        case Markup(EXPRESSION, Kind(kind)) => Some(kind)
        case Markup(EXPRESSION, _) => Some("")
        case _ => None
      }
  }


  /* citation */

  val CITATION = "citation"
  val Citation = new Markup_String(CITATION, NAME)


  /* embedded languages */

  val Symbols = new Properties.Boolean("symbols")
  val Antiquotes = new Properties.Boolean("antiquotes")
  val Delimited = new Properties.Boolean("delimited")

  val LANGUAGE = "language"
  object Language
  {
    val DOCUMENT = "document"
    val ML = "ML"
    val SML = "SML"
    val PATH = "path"
    val UNKNOWN = "unknown"

    def unapply(markup: Markup): Option[(String, Boolean, Boolean, Boolean)] =
      markup match {
        case Markup(LANGUAGE, props) =>
          (props, props, props, props) match {
            case (Name(name), Symbols(symbols), Antiquotes(antiquotes), Delimited(delimited)) =>
              Some((name, symbols, antiquotes, delimited))
            case _ => None
          }
        case _ => None
      }

    object Path
    {
      def unapply(markup: Markup): Option[Boolean] =
        markup match {
          case Language(PATH, _, _, delimited) => Some(delimited)
          case _ => None
        }
    }
  }


  /* external resources */

  val PATH = "path"
  val Path = new Markup_String(PATH, NAME)

  val EXPORT_PATH = "export_path"
  val Export_Path = new Markup_String(EXPORT_PATH, NAME)

  val URL = "url"
  val Url = new Markup_String(URL, NAME)

  val DOC = "doc"
  val Doc = new Markup_String(DOC, NAME)


  /* pretty printing */

  val Consistent = new Properties.Boolean("consistent")
  val Indent = new Properties.Int("indent")
  val Width = new Properties.Int("width")

  object Block
  {
    val name = "block"
    def apply(c: Boolean, i: Int): Markup =
      Markup(name,
        (if (c) Consistent(c) else Nil) :::
        (if (i != 0) Indent(i) else Nil))
    def unapply(markup: Markup): Option[(Boolean, Int)] =
      if (markup.name == name) {
        val c = Consistent.unapply(markup.properties).getOrElse(false)
        val i = Indent.unapply(markup.properties).getOrElse(0)
        Some((c, i))
      }
      else None
  }

  object Break
  {
    val name = "break"
    def apply(w: Int, i: Int): Markup =
      Markup(name,
        (if (w != 0) Width(w) else Nil) :::
        (if (i != 0) Indent(i) else Nil))
    def unapply(markup: Markup): Option[(Int, Int)] =
      if (markup.name == name) {
        val w = Width.unapply(markup.properties).getOrElse(0)
        val i = Indent.unapply(markup.properties).getOrElse(0)
        Some((w, i))
      }
      else None
  }

  val ITEM = "item"
  val BULLET = "bullet"

  val SEPARATOR = "separator"


  /* text properties */

  val WORDS = "words"

  val HIDDEN = "hidden"

  val DELETE = "delete"


  /* misc entities */

  val THEORY = "theory"
  val CLASS = "class"
  val TYPE_NAME = "type_name"
  val FIXED = "fixed"
  val CASE = "case"
  val CONSTANT = "constant"
  val DYNAMIC_FACT = "dynamic_fact"


  /* inner syntax */

  val TFREE = "tfree"
  val TVAR = "tvar"
  val FREE = "free"
  val SKOLEM = "skolem"
  val BOUND = "bound"
  val VAR = "var"
  val NUMERAL = "numeral"
  val LITERAL = "literal"
  val DELIMITER = "delimiter"
  val INNER_STRING = "inner_string"
  val INNER_CARTOUCHE = "inner_cartouche"

  val TOKEN_RANGE = "token_range"

  val SORTING = "sorting"
  val TYPING = "typing"
  val CLASS_PARAMETER = "class_parameter"

  val ATTRIBUTE = "attribute"
  val METHOD = "method"


  /* antiquotations */

  val ANTIQUOTED = "antiquoted"
  val ANTIQUOTE = "antiquote"

  val ML_ANTIQUOTATION = "ML_antiquotation"
  val DOCUMENT_ANTIQUOTATION = "document_antiquotation"
  val DOCUMENT_ANTIQUOTATION_OPTION = "document_antiquotation_option"


  /* document text */

  val RAW_TEXT = "raw_text"
  val PLAIN_TEXT = "plain_text"

  val PARAGRAPH = "paragraph"
  val TEXT_FOLD = "text_fold"

  object Document_Tag
  {
    val ELEMENT = "document_tag"
    val IMPORTANT = "important"
    val UNIMPORTANT = "unimportant"

    def unapply(markup: Markup): Option[String] =
      markup match {
        case Markup(ELEMENT, Name(name)) => Some(name)
        case _ => None
      }
  }


  /* Markdown document structure */

  val MARKDOWN_PARAGRAPH = "markdown_paragraph"
  val MARKDOWN_ITEM = "markdown_item"
  val Markdown_Bullet = new Markup_Int("markdown_bullet", "depth")
  val Markdown_List = new Markup_String("markdown_list", "kind")

  val ITEMIZE = "itemize"
  val ENUMERATE = "enumerate"
  val DESCRIPTION = "description"


  /* ML */

  val ML_KEYWORD1 = "ML_keyword1"
  val ML_KEYWORD2 = "ML_keyword2"
  val ML_KEYWORD3 = "ML_keyword3"
  val ML_DELIMITER = "ML_delimiter"
  val ML_TVAR = "ML_tvar"
  val ML_NUMERAL = "ML_numeral"
  val ML_CHAR = "ML_char"
  val ML_STRING = "ML_string"
  val ML_COMMENT = "ML_comment"

  val ML_DEF = "ML_def"
  val ML_OPEN = "ML_open"
  val ML_STRUCTURE = "ML_structure"
  val ML_TYPING = "ML_typing"

  val ML_BREAKPOINT = "ML_breakpoint"


  /* outer syntax */

  val COMMAND = "command"
  val KEYWORD = "keyword"
  val KEYWORD1 = "keyword1"
  val KEYWORD2 = "keyword2"
  val KEYWORD3 = "keyword3"
  val QUASI_KEYWORD = "quasi_keyword"
  val IMPROPER = "improper"
  val OPERATOR = "operator"
  val STRING = "string"
  val ALT_STRING = "alt_string"
  val VERBATIM = "verbatim"
  val CARTOUCHE = "cartouche"
  val COMMENT = "comment"

  val LOAD_COMMAND = "load_command"


  /* comments */

  val COMMENT1 = "comment1"
  val COMMENT2 = "comment2"
  val COMMENT3 = "comment3"


  /* timing */

  val Elapsed = new Properties.Double("elapsed")
  val CPU = new Properties.Double("cpu")
  val GC = new Properties.Double("gc")

  object Timing_Properties
  {
    def apply(timing: isabelle.Timing): Properties.T =
      Elapsed(timing.elapsed.seconds) ::: CPU(timing.cpu.seconds) ::: GC(timing.gc.seconds)

    def unapply(props: Properties.T): Option[isabelle.Timing] =
      (props, props, props) match {
        case (Elapsed(elapsed), CPU(cpu), GC(gc)) =>
          Some(new isabelle.Timing(Time.seconds(elapsed), Time.seconds(cpu), Time.seconds(gc)))
        case _ => None
      }

    def parse(props: Properties.T): isabelle.Timing =
      unapply(props) getOrElse isabelle.Timing.zero
  }

  val TIMING = "timing"

  object Timing
  {
    def apply(timing: isabelle.Timing): Markup = Markup(TIMING, Timing_Properties(timing))

    def unapply(markup: Markup): Option[isabelle.Timing] =
      markup match {
        case Markup(TIMING, Timing_Properties(timing)) => Some(timing)
        case _ => None
      }
  }


  /* process result */

  val Return_Code = new Properties.Int("return_code")

  object Process_Result
  {
    def apply(result: Process_Result): Properties.T =
      Return_Code(result.rc) :::
        (if (result.timing.is_zero) Nil else Timing_Properties(result.timing))

    def unapply(props: Properties.T): Option[Process_Result] =
      props match {
        case Return_Code(rc) =>
          val timing = Timing_Properties.unapply(props).getOrElse(isabelle.Timing.zero)
          Some(isabelle.Process_Result(rc, timing = timing))
        case _ => None
      }
  }


  /* command indentation */

  object Command_Indent
  {
    val name = "command_indent"
    def unapply(markup: Markup): Option[Int] =
      if (markup.name == name) Indent.unapply(markup.properties) else None
  }


  /* goals */

  val GOAL = "goal"
  val SUBGOAL = "subgoal"


  /* command status */

  val TASK = "task"

  val ACCEPTED = "accepted"
  val FORKED = "forked"
  val JOINED = "joined"
  val RUNNING = "running"
  val FINISHED = "finished"
  val FAILED = "failed"
  val CANCELED = "canceled"
  val INITIALIZED = "initialized"
  val FINALIZED = "finalized"
  val CONSOLIDATING = "consolidating"
  val CONSOLIDATED = "consolidated"


  /* interactive documents */

  val VERSION = "version"
  val ASSIGN = "assign"


  /* prover process */

  val PROVER_COMMAND = "prover_command"
  val PROVER_ARG = "prover_arg"


  /* messages */

  val INIT = "init"
  val STATUS = "status"
  val REPORT = "report"
  val RESULT = "result"
  val WRITELN = "writeln"
  val STATE = "state"
  val INFORMATION = "information"
  val TRACING = "tracing"
  val WARNING = "warning"
  val LEGACY = "legacy"
  val ERROR = "error"
  val NODES_STATUS = "nodes_status"
  val PROTOCOL = "protocol"
  val SYSTEM = "system"
  val STDOUT = "stdout"
  val STDERR = "stderr"
  val EXIT = "exit"

  val WRITELN_MESSAGE = "writeln_message"
  val STATE_MESSAGE = "state_message"
  val INFORMATION_MESSAGE = "information_message"
  val TRACING_MESSAGE = "tracing_message"
  val WARNING_MESSAGE = "warning_message"
  val LEGACY_MESSAGE = "legacy_message"
  val ERROR_MESSAGE = "error_message"

  val messages = Map(
    WRITELN -> WRITELN_MESSAGE,
    STATE -> STATE_MESSAGE,
    INFORMATION -> INFORMATION_MESSAGE,
    TRACING -> TRACING_MESSAGE,
    WARNING -> WARNING_MESSAGE,
    LEGACY -> LEGACY_MESSAGE,
    ERROR -> ERROR_MESSAGE)

  val message: String => String = messages.withDefault((s: String) => s)

  val NO_REPORT = "no_report"

  val BAD = "bad"

  val INTENSIFY = "intensify"


  /* active areas */

  val BROWSER = "browser"
  val GRAPHVIEW = "graphview"
  val THEORY_EXPORTS = "theory_exports"

  val SENDBACK = "sendback"
  val PADDING = "padding"
  val PADDING_LINE = (PADDING, "line")
  val PADDING_COMMAND = (PADDING, "command")

  val DIALOG = "dialog"
  val Result = new Properties.String(RESULT)

  val JEDIT_ACTION = "jedit_action"


  /* protocol message functions */

  val FUNCTION = "function"

  class Function(val name: String)
  {
    val PROPERTY: Properties.Entry = (FUNCTION, name)
  }

  class Properties_Function(name: String) extends Function(name)
  {
    def unapply(props: Properties.T): Option[Properties.T] =
      props match {
        case PROPERTY :: args => Some(args)
        case _ => None
      }
  }

  class Name_Function(name: String) extends Function(name)
  {
    def unapply(props: Properties.T): Option[String] =
      props match {
        case List(PROPERTY, (NAME, a)) => Some(a)
        case _ => None
      }
  }

  object ML_Statistics extends Function("ML_statistics")
  {
    def unapply(props: Properties.T): Option[(Long, String)] =
      props match {
        case List(PROPERTY, ("pid", Value.Long(pid)), ("stats_dir", stats_dir)) =>
          Some((pid, stats_dir))
        case _ => None
      }
  }

  val command_timing_properties: Set[String] = Set(FILE, OFFSET, NAME, Elapsed.name)
  def command_timing_property(entry: Properties.Entry): Boolean = command_timing_properties(entry._1)

  object Command_Timing extends Properties_Function("command_timing")
  object Theory_Timing extends Properties_Function("theory_timing")
  object Session_Timing extends Properties_Function("session_timing")
  {
    val Threads = new Properties.Int("threads")
  }
  object Task_Statistics extends Properties_Function("task_statistics")

  object Loading_Theory extends Properties_Function("loading_theory")
  object Build_Session_Finished extends Function("build_session_finished")

  object Commands_Accepted extends Function("commands_accepted")
  object Assign_Update extends Function("assign_update")
  object Removed_Versions extends Function("removed_versions")

  object Invoke_Scala extends Function("invoke_scala")
  {
    def unapply(props: Properties.T): Option[(String, String, Boolean)] =
      props match {
        case List(PROPERTY, (NAME, name), (ID, id), ("thread", Value.Boolean(thread))) =>
          Some((name, id, thread))
        case _ => None
      }
  }

  object Cancel_Scala extends Function("cancel_scala")
  {
    def unapply(props: Properties.T): Option[String] =
      props match {
        case List(PROPERTY, (ID, id)) => Some(id)
        case _ => None
      }
  }

  val PRINT_OPERATIONS = "print_operations"


  /* export */

  val EXPORT = "export"
  val THEORY_NAME = "theory_name"
  val EXECUTABLE = "executable"
  val COMPRESS = "compress"
  val STRICT = "strict"


  /* debugger output */

  val DEBUGGER_STATE = "debugger_state"
  object Debugger_State
  {
    def unapply(props: Properties.T): Option[String] =
      props match {
        case List((FUNCTION, DEBUGGER_STATE), (NAME, name)) => Some(name)
        case _ => None
      }
  }

  val DEBUGGER_OUTPUT = "debugger_output"
  object Debugger_Output
  {
    def unapply(props: Properties.T): Option[String] =
      props match {
        case List((FUNCTION, DEBUGGER_OUTPUT), (NAME, name)) => Some(name)
        case _ => None
      }
  }


  /* simplifier trace */

  val SIMP_TRACE_PANEL = "simp_trace_panel"

  val SIMP_TRACE_LOG = "simp_trace_log"
  val SIMP_TRACE_STEP = "simp_trace_step"
  val SIMP_TRACE_RECURSE = "simp_trace_recurse"
  val SIMP_TRACE_HINT = "simp_trace_hint"
  val SIMP_TRACE_IGNORE = "simp_trace_ignore"

  val SIMP_TRACE_CANCEL = "simp_trace_cancel"
  object Simp_Trace_Cancel
  {
    def unapply(props: Properties.T): Option[Long] =
      props match {
        case (FUNCTION, SIMP_TRACE_CANCEL) :: Serial(i) => Some(i)
        case _ => None
      }
  }


  /* XML data representation */

  def encode: XML.Encode.T[Markup] = (markup: Markup) =>
  {
    import XML.Encode._
    pair(string, properties)((markup.name, markup.properties))
  }

  def decode: XML.Decode.T[Markup] = (body: XML.Body) =>
  {
    import XML.Decode._
    val (name, props) = pair(string, properties)(body)
    Markup(name, props)
  }
}


sealed case class Markup(name: String, properties: Properties.T)
{
  def markup(s: String): String =
    YXML.string_of_tree(XML.Elem(this, List(XML.Text(s))))

  def update_properties(more_props: Properties.T): Markup =
    if (more_props.isEmpty) this
    else Markup(name, more_props.foldRight(properties) { case (p, ps) => Properties.put(ps, p) })

  def + (entry: Properties.Entry): Markup =
    Markup(name, Properties.put(properties, entry))
}
