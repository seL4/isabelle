/*  Title:      Pure/PIDE/protocol.scala
    Author:     Makarius

Protocol message formats for interactive proof documents.
*/

package isabelle


object Protocol
{
  /* markers for inlined messages */

  val Loading_Theory_Marker = Protocol_Message.Marker("loading_theory")
  val Meta_Info_Marker = Protocol_Message.Marker("meta_info")
  val Command_Timing_Marker = Protocol_Message.Marker("command_timing")
  val Theory_Timing_Marker = Protocol_Message.Marker("theory_timing")
  val Session_Timing_Marker = Protocol_Message.Marker("session_timing")
  val ML_Statistics_Marker = Protocol_Message.Marker("ML_statistics")
  val Task_Statistics_Marker = Protocol_Message.Marker("task_statistics")
  val Error_Message_Marker = Protocol_Message.Marker("error_message")


  /* batch build */

  object Loading_Theory
  {
    def unapply(props: Properties.T): Option[(Document.Node.Name, Document_ID.Exec)] =
      (props, props, props) match {
        case (Markup.Name(name), Position.File(file), Position.Id(id))
        if Path.is_wellformed(file) =>
          val master_dir = Path.explode(file).dir.implode
          Some((Document.Node.Name(file, master_dir, name), id))
        case _ => None
      }
  }


  /* document editing */

  object Commands_Accepted
  {
    def unapply(text: String): Option[List[Document_ID.Command]] =
      try { Some(space_explode(',', text).map(Value.Long.parse)) }
      catch { case ERROR(_) => None }

    val message: XML.Elem = XML.elem(Markup.STATUS, List(XML.elem(Markup.ACCEPTED)))
  }

  object Assign_Update
  {
    def unapply(text: String)
      : Option[(Document_ID.Version, List[String], Document.Assign_Update)] =
    {
      try {
        import XML.Decode._
        def decode_upd(body: XML.Body): (Long, List[Long]) =
          space_explode(',', string(body)).map(Value.Long.parse) match {
            case a :: bs => (a, bs)
            case _ => throw new XML.XML_Body(body)
          }
        Some(triple(long, list(string), list(decode_upd))(Symbol.decode_yxml(text)))
      }
      catch {
        case ERROR(_) => None
        case _: XML.Error => None
      }
    }
  }

  object Removed
  {
    def unapply(text: String): Option[List[Document_ID.Version]] =
      try {
        import XML.Decode._
        Some(list(long)(Symbol.decode_yxml(text)))
      }
      catch {
        case ERROR(_) => None
        case _: XML.Error => None
      }
  }


  /* command timing */

  object Command_Timing
  {
    def unapply(props: Properties.T): Option[(Properties.T, Document_ID.Generic, isabelle.Timing)] =
      props match {
        case Markup.Command_Timing(args) =>
          (args, args) match {
            case (Position.Id(id), Markup.Timing_Properties(timing)) => Some((args, id, timing))
            case _ => None
          }
        case _ => None
      }
  }


  /* theory timing */

  object Theory_Timing
  {
    def unapply(props: Properties.T): Option[(String, isabelle.Timing)] =
      props match {
        case Markup.Theory_Timing(args) =>
          (args, args) match {
            case (Markup.Name(name), Markup.Timing_Properties(timing)) => Some((name, timing))
            case _ => None
          }
        case _ => None
      }
  }


  /* result messages */

  def is_message(pred: XML.Elem => Boolean, body: XML.Body): Boolean =
    body match {
      case List(elem: XML.Elem) => pred(elem)
      case _ => false
    }

  def is_result(msg: XML.Tree): Boolean =
    msg match {
      case XML.Elem(Markup(Markup.RESULT, _), _) => true
      case _ => false
    }

  def is_tracing(msg: XML.Tree): Boolean =
    msg match {
      case XML.Elem(Markup(Markup.TRACING, _), _) => true
      case XML.Elem(Markup(Markup.TRACING_MESSAGE, _), _) => true
      case _ => false
    }

  def is_state(msg: XML.Tree): Boolean =
    msg match {
      case XML.Elem(Markup(Markup.STATE, _), _) => true
      case XML.Elem(Markup(Markup.STATE_MESSAGE, _), _) => true
      case _ => false
    }

  def is_information(msg: XML.Tree): Boolean =
    msg match {
      case XML.Elem(Markup(Markup.INFORMATION, _), _) => true
      case XML.Elem(Markup(Markup.INFORMATION_MESSAGE, _), _) => true
      case _ => false
    }

  def is_writeln(msg: XML.Tree): Boolean =
    msg match {
      case XML.Elem(Markup(Markup.WRITELN, _), _) => true
      case XML.Elem(Markup(Markup.WRITELN_MESSAGE, _), _) => true
      case _ => false
    }

  def is_warning(msg: XML.Tree): Boolean =
    msg match {
      case XML.Elem(Markup(Markup.WARNING, _), _) => true
      case XML.Elem(Markup(Markup.WARNING_MESSAGE, _), _) => true
      case _ => false
    }

  def is_legacy(msg: XML.Tree): Boolean =
    msg match {
      case XML.Elem(Markup(Markup.LEGACY, _), _) => true
      case XML.Elem(Markup(Markup.LEGACY_MESSAGE, _), _) => true
      case _ => false
    }

  def is_error(msg: XML.Tree): Boolean =
    msg match {
      case XML.Elem(Markup(Markup.ERROR, _), _) => true
      case XML.Elem(Markup(Markup.ERROR_MESSAGE, _), _) => true
      case _ => false
    }

  def is_inlined(msg: XML.Tree): Boolean =
    !(is_result(msg) || is_tracing(msg) || is_state(msg))

  def is_exported(msg: XML.Tree): Boolean =
    is_writeln(msg) || is_warning(msg) || is_legacy(msg) || is_error(msg)

  def message_text(body: XML.Body,
    margin: Double = Pretty.default_margin,
    breakgain: Double = Pretty.default_breakgain,
    metric: Pretty.Metric = Pretty.Default_Metric): String =
  {
    val text =
      Pretty.string_of(Protocol_Message.expose_no_reports(body),
        margin = margin, breakgain = breakgain, metric = metric)

    if (is_message(is_warning, body) || is_message(is_legacy, body)) Output.warning_prefix(text)
    else if (is_message(is_error, body)) Output.error_prefix(text)
    else text
  }


  /* export */

  object Export
  {
    sealed case class Args(
      id: Option[String] = None,
      serial: Long = 0L,
      theory_name: String,
      name: String,
      executable: Boolean = false,
      compress: Boolean = true,
      strict: Boolean = true)
    {
      def compound_name: String = isabelle.Export.compound_name(theory_name, name)
    }

    def unapply(props: Properties.T): Option[Args] =
      props match {
        case
          List(
            (Markup.FUNCTION, Markup.EXPORT),
            (Markup.ID, id),
            (Markup.SERIAL, Value.Long(serial)),
            (Markup.THEORY_NAME, theory_name),
            (Markup.NAME, name),
            (Markup.EXECUTABLE, Value.Boolean(executable)),
            (Markup.COMPRESS, Value.Boolean(compress)),
            (Markup.STRICT, Value.Boolean(strict))) =>
          Some(Args(proper_string(id), serial, theory_name, name, executable, compress, strict))
        case _ => None
      }
  }


  /* breakpoints */

  object ML_Breakpoint
  {
    def unapply(tree: XML.Tree): Option[Long] =
    tree match {
      case XML.Elem(Markup(Markup.ML_BREAKPOINT, Markup.Serial(breakpoint)), _) => Some(breakpoint)
      case _ => None
    }
  }


  /* dialogs */

  object Dialog_Args
  {
    def unapply(props: Properties.T): Option[(Document_ID.Generic, Long, String)] =
      (props, props, props) match {
        case (Position.Id(id), Markup.Serial(serial), Markup.Result(result)) =>
          Some((id, serial, result))
        case _ => None
      }
  }

  object Dialog
  {
    def unapply(tree: XML.Tree): Option[(Document_ID.Generic, Long, String)] =
      tree match {
        case XML.Elem(Markup(Markup.DIALOG, Dialog_Args(id, serial, result)), _) =>
          Some((id, serial, result))
        case _ => None
      }
  }

  object Dialog_Result
  {
    def apply(id: Document_ID.Generic, serial: Long, result: String): XML.Elem =
    {
      val props = Position.Id(id) ::: Markup.Serial(serial)
      XML.Elem(Markup(Markup.RESULT, props), List(XML.Text(result)))
    }

    def unapply(tree: XML.Tree): Option[String] =
      tree match {
        case XML.Elem(Markup(Markup.RESULT, _), List(XML.Text(result))) => Some(result)
        case _ => None
      }
  }
}


trait Protocol
{
  /* protocol commands */

  def protocol_command_raw(name: String, args: List[Bytes]): Unit
  def protocol_command_args(name: String, args: List[String])
  def protocol_command(name: String, args: String*): Unit


  /* options */

  def options(opts: Options): Unit =
    protocol_command("Prover.options", Symbol.encode_yxml(opts.encode))


  /* resources */

  def init_session(resources: Resources): Unit =
    protocol_command("Prover.init_session", resources.init_session_yxml)


  /* interned items */

  def define_blob(digest: SHA1.Digest, bytes: Bytes): Unit =
    protocol_command_raw("Document.define_blob", List(Bytes(digest.toString), bytes))

  private def encode_command(command: Command): (String, String, String, String, List[String]) =
  {
    import XML.Encode._

    val blobs_yxml =
    {
      val encode_blob: T[Exn.Result[Command.Blob]] =
        variant(List(
          { case Exn.Res(Command.Blob(a, b, c)) =>
              (Nil, triple(string, string, option(string))(
                (a.node, b.implode, c.map(p => p._1.toString)))) },
          { case Exn.Exn(e) => (Nil, string(Exn.message(e))) }))

      Symbol.encode_yxml(pair(list(encode_blob), int)(command.blobs, command.blobs_index))
    }

    val toks_yxml =
    {
      val encode_tok: T[Token] = (tok => pair(int, int)((tok.kind.id, Symbol.length(tok.source))))
      Symbol.encode_yxml(list(encode_tok)(command.span.content))
    }
    val toks_sources = command.span.content.map(tok => Symbol.encode(tok.source))

    (Document_ID(command.id), Symbol.encode(command.span.name), blobs_yxml, toks_yxml, toks_sources)
  }

  def define_command(command: Command)
  {
    val (command_id, name, blobs_yxml, toks_yxml, toks_sources) = encode_command(command)
    protocol_command_args(
      "Document.define_command", command_id :: name :: blobs_yxml :: toks_yxml :: toks_sources)
  }

  def define_commands(commands: List[Command])
  {
    protocol_command_args("Document.define_commands",
      commands.map(command =>
      {
        import XML.Encode._
        val (command_id, name, blobs_yxml, toks_yxml, toks_sources) = encode_command(command)
        val body =
          pair(string, pair(string, pair(string, pair(string, list(string)))))(
            command_id, (name, (blobs_yxml, (toks_yxml, toks_sources))))
        YXML.string_of_body(body)
      }))
  }

  def define_commands_bulk(commands: List[Command])
  {
    val (irregular, regular) = commands.partition(command => YXML.detect(command.source))
    irregular.foreach(define_command)
    regular match {
      case Nil =>
      case List(command) => define_command(command)
      case _ => define_commands(regular)
    }
  }


  /* execution */

  def discontinue_execution(): Unit =
    protocol_command("Document.discontinue_execution")

  def cancel_exec(id: Document_ID.Exec): Unit =
    protocol_command("Document.cancel_exec", Document_ID(id))


  /* document versions */

  def update(old_id: Document_ID.Version, new_id: Document_ID.Version,
    edits: List[Document.Edit_Command], consolidate: List[Document.Node.Name])
  {
    val consolidate_yxml =
    {
      import XML.Encode._
      Symbol.encode_yxml(list(string)(consolidate.map(_.node)))
    }
    val edits_yxml =
    {
      import XML.Encode._
      def id: T[Command] = (cmd => long(cmd.id))
      def encode_edit(name: Document.Node.Name)
          : T[Document.Node.Edit[Command.Edit, Command.Perspective]] =
        variant(List(
          { case Document.Node.Edits(a) => (Nil, list(pair(option(id), option(id)))(a)) },
          { case Document.Node.Deps(header) =>
              val master_dir = File.standard_url(name.master_dir)
              val imports = header.imports.map(_.node)
              val keywords = header.keywords.map({ case (a, spec) => (a, (spec.kind, spec.tags)) })
              (Nil,
                pair(string, pair(string, pair(list(string),
                  pair(list(pair(string, pair(string, list(string)))), list(string)))))(
                (master_dir, (name.theory, (imports, (keywords, header.errors)))))) },
          { case Document.Node.Perspective(a, b, c) =>
              (bool_atom(a) :: b.commands.map(cmd => long_atom(cmd.id)),
                list(pair(id, pair(string, list(string))))(c.dest)) }))
      edits.map({ case (name, edit) =>
        Symbol.encode_yxml(pair(string, encode_edit(name))(name.node, edit)) })
    }
    protocol_command_args("Document.update",
      Document_ID(old_id) :: Document_ID(new_id) :: consolidate_yxml :: edits_yxml)
  }

  def remove_versions(versions: List[Document.Version])
  {
    val versions_yxml =
    { import XML.Encode._
      Symbol.encode_yxml(list(long)(versions.map(_.id))) }
    protocol_command("Document.remove_versions", versions_yxml)
  }


  /* dialog via document content */

  def dialog_result(serial: Long, result: String): Unit =
    protocol_command("Document.dialog_result", Value.Long(serial), result)
}
