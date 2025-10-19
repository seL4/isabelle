/*  Title:      Pure/PIDE/markup.scala
    Author:     Makarius

Quasi-abstract markup elements.
*/

package isabelle


object Markup {
  /* elements */

  object Elements {
    def apply(elems: Set[String]): Elements = new Elements(elems)
    def apply(elems: String*): Elements = apply(Set(elems: _*))
    val empty: Elements = apply()
    val full: Elements =
      new Elements(Set.empty) {
        override def apply(elem: String): Boolean = true
        override def toString: String = "Elements.full"
      }
  }

  sealed class Elements private[Markup](private val rep: Set[String]) {
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

  class Markup_Elem(val name: String) {
    def apply(props: Properties.T = Nil): Markup = Markup(name, props)
    def unapply(markup: Markup): Option[Properties.T] =
      if (markup.name == name) Some(markup.properties) else None
  }

  class Markup_String(val name: String, prop: String) {
    val Prop: Properties.String = new Properties.String(prop)

    def apply(s: String): Markup = Markup(name, Prop(s))
    def unapply(markup: Markup): Option[String] =
      if (markup.name == name) Prop.unapply(markup.properties) else None
    def get(markup: Markup): String = unapply(markup).getOrElse("")
  }

  class Markup_Int(val name: String, prop: String) {
    val Prop: Properties.Int = new Properties.Int(prop)

    def apply(i: Int): Markup = Markup(name, Prop(i))
    def unapply(markup: Markup): Option[Int] =
      if (markup.name == name) Prop.unapply(markup.properties) else None
    def get(markup: Markup): Int = unapply(markup).getOrElse(0)
  }

  class Markup_Long(val name: String, prop: String) {
    val Prop: Properties.Long = new Properties.Long(prop)

    def apply(i: Long): Markup = Markup(name, Prop(i))
    def unapply(markup: Markup): Option[Long] =
      if (markup.name == name) Prop.unapply(markup.properties) else None
    def get(markup: Markup): Long = unapply(markup).getOrElse(0)
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

  object Entity {
    val Def = new Markup_Long(ENTITY, "def")
    val Ref = new Markup_Long(ENTITY, "ref")

    object Occ {
      def unapply(markup: Markup): Option[Long] =
        Def.unapply(markup) orElse Ref.unapply(markup)
    }

    def unapply(markup: Markup): Option[(String, String)] =
      markup match {
        case Markup(ENTITY, props) => Some((Kind.get(props), Name.get(props)))
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
  val LABEL = "label"
  val FILE = "file"
  val ID = "id"

  val DEF_LINE = "def_line"
  val DEF_OFFSET = "def_offset"
  val DEF_END_OFFSET = "def_end_offset"
  val DEF_LABEL = "def_label"
  val DEF_FILE = "def_file"
  val DEF_ID = "def_id"

  val POSITION = "position"

  val POSITION_PROPERTIES = Set(LINE, OFFSET, END_OFFSET, LABEL, FILE, ID)
  def position_property(entry: Properties.Entry): Boolean = POSITION_PROPERTIES(entry._1)


  /* position "def" name */

  private val def_names: Map[String, String] =
    Map(LINE -> DEF_LINE, OFFSET -> DEF_OFFSET, END_OFFSET -> DEF_END_OFFSET,
      LABEL -> DEF_LABEL, FILE -> DEF_FILE, ID -> DEF_ID)

  def def_name(a: String): String = def_names.getOrElse(a, a + "def_")


  /* notation */

  val NOTATION = "notation"
  object Notation {
    def unapply(markup: Markup): Option[(String, String)] =
      markup match {
        case Markup(NOTATION, props) => Some((Kind.get(props), Name.get(props)))
        case _ => None
      }
  }


  /* expression */

  val EXPRESSION = "expression"
  object Expression {
    def unapply(markup: Markup): Option[(String, String)] =
      markup match {
        case Markup(EXPRESSION, props) => Some((Kind.get(props), Name.get(props)))
        case _ => None
      }

    val item: Markup = Markup(EXPRESSION, Kind(ITEM))
  }


  /* citation */

  val CITATION = "citation"
  val Citation = new Markup_String(CITATION, NAME)


  /* embedded languages */

  val Symbols = new Properties.Boolean("symbols")
  val Antiquotes = new Properties.Boolean("antiquotes")
  val Delimited = new Properties.Boolean("delimited")

  val LANGUAGE = "language"
  object Language {
    val DOCUMENT = "document"
    val ANTIQUOTATION = "antiquotation"
    val ML = "ML"
    val SML = "SML"
    val PATH = "path"
    val UNKNOWN = "unknown"

    def apply(name: String, symbols: Boolean, antiquotes: Boolean, delimited: Boolean): Language =
      new Language(name, symbols, antiquotes, delimited)

    val outer: Language = apply("", true, false, false)

    def unapply(markup: Markup): Option[Language] =
      markup match {
        case Markup(LANGUAGE, props) =>
          (props, props, props, props) match {
            case (Name(name), Symbols(symbols), Antiquotes(antiquotes), Delimited(delimited)) =>
              Some(apply(name, symbols, antiquotes, delimited))
            case _ => None
          }
        case _ => None
      }
  }
  class Language private(
    val name: String,
    val symbols: Boolean,
    val antiquotes: Boolean,
    val delimited: Boolean
  ) {
    override def toString: String = name

    def is_document: Boolean = name == Language.DOCUMENT
    def is_antiquotation: Boolean = name == Language.ANTIQUOTATION
    def is_path: Boolean = name == Language.PATH

    def description: String = Word.informal(name)
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

  object Block {
    val name = "block"
    def apply(consistent: Boolean = false, indent: Int = 0): Markup =
      Markup(name,
        (if (consistent) Consistent(consistent) else Nil) :::
        (if (indent != 0) Indent(indent) else Nil))
    def unapply(markup: Markup): Option[(Boolean, Int)] =
      if (markup.name == name) {
        val consistent = Consistent.get(markup.properties)
        val indent = Indent.get(markup.properties)
        Some((consistent, indent))
      }
      else None
  }

  object Break {
    val name = "break"
    def apply(width: Int = 0, indent: Int = 0): Markup =
      Markup(name,
        (if (width != 0) Width(width) else Nil) :::
        (if (indent != 0) Indent(indent) else Nil))
    def unapply(markup: Markup): Option[(Int, Int)] =
      if (markup.name == name) {
        val width = Width.get(markup.properties)
        val indent = Indent.get(markup.properties)
        Some((width, indent))
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

  val SESSION = "session"

  val THEORY = "theory"
  val CLASS = "class"
  val LOCALE = "locale"
  val BUNDLE = "bundle"
  val TYPE_NAME = "type_name"
  val CONSTANT = "constant"
  val AXIOM = "axiom"
  val FACT = "fact"
  val ORACLE = "oracle"

  val FIXED = "fixed"
  val CASE = "case"
  val DYNAMIC_FACT = "dynamic_fact"
  val LITERAL_FACT = "literal_fact"

  val ATTRIBUTE = "attribute"
  val METHOD = "method"
  val METHOD_MODIFIER = "method_modifier"


  /* inner syntax */

  val TCLASS = "tclass"
  val TCONST = "tconst"
  val TFREE = "tfree"
  val TVAR = "tvar"
  val CONST = "const"
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

  object Document_Tag extends Markup_String("document_tag", NAME) {
    val IMPORTANT = "important"
    val UNIMPORTANT = "unimportant"
  }


  /* HTML */

  val RAW_HTML = "raw_html"


  /* LaTeX */

  val Document_Latex = new Markup_Elem("document_latex")

  val Latex_Output = new Markup_Elem("latex_output")
  val Latex_Macro0 = new Markup_String("latex_macro0", NAME)
  val Latex_Macro = new Markup_String("latex_macro", NAME)
  val Latex_Environment = new Markup_String("latex_environment", NAME)
  val Latex_Heading = new Markup_String("latex_heading", KIND)
  val Latex_Body = new Markup_String("latex_body", KIND)
  val Latex_Delim = new Markup_String("latex_delim", NAME)
  val Latex_Tag = new Markup_String("latex_tag", NAME)

  val Latex_Cite = new Markup_Elem("latex_cite")
  val Citations = new Properties.String("citations")

  val Latex_Index_Item = new Markup_Elem("latex_index_item")
  val Latex_Index_Entry = new Markup_String("latex_index_entry", KIND)

  val Optional_Argument = new Properties.String("optional_argument")


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

  val COMMAND_SPAN = "command_span"
  object Command_Span {
    val Is_Begin = new Properties.Boolean("is_begin")

    sealed case class Args(name: String, kind: String, is_begin: Boolean) {
      def properties: Properties.T =
        (if (name.isEmpty) Nil else Name(name)) :::
        (if (kind.isEmpty) Nil else Kind(kind)) :::
        (if (!is_begin) Nil else Is_Begin(is_begin))
    }

    def apply(args: Args): Markup = Markup(COMMAND_SPAN, args.properties)
    def apply(name: String, kind: String, is_begin: Boolean): Markup =
      apply(Args(name, kind, is_begin))

    def unapply(markup: Markup): Option[Args] =
      if (markup.name == COMMAND_SPAN) {
        val props = markup.properties
        Some(Args(Name.get(props), Kind.get(props), Is_Begin.get(props)))
      }
      else None
  }

  val COMMAND_RANGE = "command_range"

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
  val CARTOUCHE = "cartouche"
  val COMMENT = "comment"

  val LOAD_COMMAND = "load_command"


  /* comments */

  val COMMENT1 = "comment1"
  val COMMENT2 = "comment2"
  val COMMENT3 = "comment3"


  /* concrete syntax (notably mixfix notation) */

  val Syntax = new Properties.Boolean("syntax")

  def has_syntax(props: Properties.T): Boolean = Syntax.get(props)


  /* timing */

  val Elapsed = new Properties.Double("elapsed")
  val CPU = new Properties.Double("cpu")
  val GC = new Properties.Double("gc")

  object Timing_Properties {
    def apply(timing: isabelle.Timing): Properties.T =
      Elapsed(timing.elapsed.seconds) ::: CPU(timing.cpu.seconds) ::: GC(timing.gc.seconds)

    def get(props: Properties.T): isabelle.Timing = {
      val elapsed = Time.seconds(Elapsed.get(props))
      val cpu = Time.seconds(CPU.get(props))
      val gc = Time.seconds(GC.get(props))
      isabelle.Timing.make(elapsed, cpu, gc)
    }
  }


  /* process result */

  val Return_Code = new Properties.Int("return_code")

  object Process_Result {
    def apply(result: Process_Result): Properties.T =
      Return_Code(result.rc) :::
        (if (result.timing.is_zero) Nil else Timing_Properties(result.timing))

    def unapply(props: Properties.T): Option[Process_Result] =
      props match {
        case Return_Code(rc) =>
          Some(isabelle.Process_Result(rc, timing = Timing_Properties.get(props)))
        case _ => None
      }
  }


  /* command indentation */

  val Command_Indent = new Markup_Int("command_indent", Indent.name)


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

  val command_running: Properties.Entry = (COMMAND, RUNNING)


  /* interactive documents */

  val VERSION = "version"
  val ASSIGN = "assign"


  /* prover process */

  val PROVER_COMMAND = "prover_command"
  val PROVER_ARG = "prover_arg"


  /* messages */

  val Urgent = new Properties.Boolean("urgent")

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
  object Bad {
    def apply(serial: Long): Markup = Markup(BAD, Serial(serial))
    def unapply(markup: Markup): Option[Long] =
      markup match {
        case Markup(BAD, Serial(i)) => Some(i)
        case _ => None
      }
  }

  val INTENSIFY = "intensify"


  /* ML profiling */

  val COUNT = "count"
  val ML_PROFILING_ENTRY = "ML_profiling_entry"
  val ML_PROFILING = "ML_profiling"

  object ML_Profiling {
    def unapply_entry(tree: XML.Tree): Option[isabelle.ML_Profiling.Entry] =
      tree match {
        case XML.Elem(Markup(ML_PROFILING_ENTRY, List((NAME, name), (COUNT, Value.Long(count)))), _) =>
          Some(isabelle.ML_Profiling.Entry(name, count))
        case _ => None
      }

    def unapply_report(tree: XML.Tree): Option[isabelle.ML_Profiling.Report] =
      tree match {
        case XML.Elem(Markup(ML_PROFILING, List((KIND, kind))), body) =>
          Some(isabelle.ML_Profiling.Report(kind, body.flatMap(unapply_entry)))
        case _ => None
      }
  }


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

  class Function(val name: String) {
    val THIS: Properties.Entry = (FUNCTION, name)
  }

  class Properties_Function(name: String) extends Function(name) {
    def unapply(props: Properties.T): Option[Properties.T] =
      props match {
        case THIS :: args => Some(args)
        case _ => None
      }
  }

  class Name_Function(name: String) extends Function(name) {
    def unapply(props: Properties.T): Option[String] =
      props match {
        case List(THIS, (NAME, a)) => Some(a)
        case _ => None
      }
  }

  object ML_Statistics extends Function("ML_statistics") {
    def unapply(props: Properties.T): Option[(Long, String)] =
      props match {
        case List(THIS, ("pid", Value.Long(pid)), ("stats_dir", stats_dir)) =>
          Some((pid, stats_dir))
        case _ => None
      }
  }

  val Command_Offset = new Properties.Int("command_offset")
  private val command_timing_exports: Set[String] = Set(FILE, OFFSET, NAME, Elapsed.name)
  def command_timing_export(entry: Properties.Entry): Boolean = command_timing_exports(entry._1)

  object Command_Timing extends Properties_Function("command_timing")
  object Session_Timing extends Properties_Function("session_timing") {
    val Threads = new Properties.Int("threads")
  }
  object Task_Statistics extends Properties_Function("task_statistics")

  val Commands = new Properties.Int("commands")
  object Loading_Theory extends Properties_Function("loading_theory")
  object Build_Session_Finished extends Function("build_session_finished")

  object Commands_Accepted extends Function("commands_accepted")
  object Assign_Update extends Function("assign_update")
  object Removed_Versions extends Function("removed_versions")

  object Invoke_Scala extends Function("invoke_scala") {
    def unapply(props: Properties.T): Option[(String, String)] =
      props match {
        case List(THIS, (NAME, name), (ID, id)) => Some((name, id))
        case _ => None
      }
  }

  object Cancel_Scala extends Function("cancel_scala") {
    def unapply(props: Properties.T): Option[String] =
      props match {
        case List(THIS, (ID, id)) => Some(id)
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
  object Debugger_State {
    def unapply(props: Properties.T): Option[String] =
      props match {
        case List((FUNCTION, DEBUGGER_STATE), (NAME, name)) => Some(name)
        case _ => None
      }
  }

  val DEBUGGER_OUTPUT = "debugger_output"
  object Debugger_Output {
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
  object Simp_Trace_Cancel {
    def unapply(props: Properties.T): Option[Long] =
      props match {
        case (FUNCTION, SIMP_TRACE_CANCEL) :: Serial(i) => Some(i)
        case _ => None
      }
  }


  /* XML data representation */

  def encode: XML.Encode.T[Markup] = { (markup: Markup) =>
    import XML.Encode._
    pair(string, properties)((markup.name, markup.properties))
  }

  def decode: XML.Decode.T[Markup] = { (body: XML.Body) =>
    import XML.Decode._
    val (name, props) = pair(string, properties)(body)
    Markup(name, props)
  }
}


sealed case class Markup(name: String, properties: Properties.T) {
  def is_empty: Boolean = name.isEmpty

  def position_properties: Position.T = properties.filter(Markup.position_property)

  def markup(s: String): String =
    YXML.string_of_tree(XML.Elem(this, List(XML.Text(s))))

  def update_properties(more_props: Properties.T): Markup =
    if (more_props.isEmpty) this
    else Markup(name, more_props.foldRight(properties) { case (p, ps) => Properties.put(ps, p) })

  def + (entry: Properties.Entry): Markup =
    Markup(name, Properties.put(properties, entry))
}
