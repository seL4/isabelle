/*  Title:      Pure/PIDE/protocol.scala
    Author:     Makarius

Protocol message formats for interactive proof documents.
*/

package isabelle


object Protocol {
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

  object Loading_Theory {
    def unapply(props: Properties.T): Option[(Document.Node.Name, Document_ID.Exec)] =
      (props, props, props) match {
        case (Markup.Name(theory), Position.File(file), Position.Id(id))
        if Path.is_wellformed(file) => Some((Document.Node.Name(file, theory = theory), id))
        case _ => None
      }
  }


  /* document editing */

  object Commands_Accepted {
    def unapply(text: String): Option[List[Document_ID.Command]] =
      try { Some(space_explode(',', text).map(Value.Long.parse)) }
      catch { case ERROR(_) => None }

    val message: XML.Elem = XML.elem(Markup.STATUS, List(XML.elem(Markup.ACCEPTED)))
  }

  object Assign_Update {
    def unapply(
      text: String
    ) : Option[(Document_ID.Version, List[String], Document.Assign_Update)] = {
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

  object Removed {
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

  object Command_Timing {
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

  object Theory_Timing {
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
    !(is_result(msg) || is_tracing(msg))

  def is_exported(msg: XML.Tree): Boolean =
    is_writeln(msg) || is_warning(msg) || is_legacy(msg) || is_error(msg)

  def message_heading(elem: XML.Elem, pos: Position.T): String = {
    val h =
      if (is_warning(elem) || is_legacy(elem)) "Warning"
      else if (is_error(elem)) "Error"
      else if (is_information(elem)) "Information"
      else if (is_tracing(elem)) "Tracing"
      else if (is_state(elem)) "State"
      else "Output"
    h + Position.here(pos)
  }

  def message_text(elem: XML.Elem,
    heading: Boolean = false,
    pos: Position.T = Position.none,
    margin: Double = Pretty.default_margin,
    breakgain: Double = Pretty.default_breakgain,
    metric: Pretty.Metric = Pretty.Default_Metric
  ): String = {
    val text1 = if (heading) "\n" + message_heading(elem, pos) + ":\n" else ""

    val body =
      Pretty.string_of(Protocol_Message.expose_no_reports(List(elem)),
        margin = margin, breakgain = breakgain, metric = metric)

    val text2 =
      if (is_warning(elem) || is_legacy(elem)) Output.warning_prefix(body)
      else if (is_error(elem)) Output.error_message_prefix(body)
      else body

    text1 + text2
  }

  def make_message(body: XML.Body, kind: String, props: Properties.T = Nil): XML.Elem =
    XML.Elem(Markup(Markup.message(kind), props), body)

  def writeln_message(body: XML.Body): XML.Elem = make_message(body, Markup.WRITELN)
  def warning_message(body: XML.Body): XML.Elem = make_message(body, Markup.WARNING)
  def error_message(body: XML.Body): XML.Elem = make_message(body, Markup.ERROR)

  def writeln_message(msg: String): XML.Elem = writeln_message(XML.string(msg))
  def warning_message(msg: String): XML.Elem = warning_message(XML.string(msg))
  def error_message(msg: String): XML.Elem = error_message(XML.string(msg))


  /* ML profiling */

  object ML_Profiling {
    def unapply(msg: XML.Tree): Option[isabelle.ML_Profiling.Report] =
      msg match {
        case XML.Elem(_, List(tree)) if is_tracing(msg) =>
          Markup.ML_Profiling.unapply_report(tree)
        case _ => None
      }
  }


  /* export */

  object Export {
    sealed case class Args(
      id: Option[String] = None,
      serial: Long = 0L,
      theory_name: String,
      name: String,
      executable: Boolean = false,
      compress: Boolean = true,
      strict: Boolean = true
    ) {
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

  object ML_Breakpoint {
    def unapply(tree: XML.Tree): Option[Long] =
    tree match {
      case XML.Elem(Markup(Markup.ML_BREAKPOINT, Markup.Serial(breakpoint)), _) => Some(breakpoint)
      case _ => None
    }
  }


  /* dialogs */

  object Dialog_Args {
    def unapply(props: Properties.T): Option[(Document_ID.Generic, Long, String)] =
      (props, props, props) match {
        case (Position.Id(id), Markup.Serial(serial), Markup.Result(result)) =>
          Some((id, serial, result))
        case _ => None
      }
  }

  object Dialog {
    def unapply(tree: XML.Tree): Option[(Document_ID.Generic, Long, String)] =
      tree match {
        case XML.Elem(Markup(Markup.DIALOG, Dialog_Args(id, serial, result)), _) =>
          Some((id, serial, result))
        case _ => None
      }
  }

  object Dialog_Result {
    def apply(id: Document_ID.Generic, serial: Long, result: String): XML.Elem = {
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


trait Protocol {
  /* protocol commands */

  def protocol_command_raw(name: String, args: List[Bytes]): Unit
  def protocol_command_args(name: String, args: List[XML.Body]): Unit
  def protocol_command(name: String, args: XML.Body*): Unit


  /* options */

  def options(opts: Options): Unit =
    protocol_command("Prover.options", opts.encode)


  /* resources */

  def init_session(resources: Resources): Unit =
    protocol_command("Prover.init_session", resources.init_session_xml)


  /* interned items */

  def define_blob(digest: SHA1.Digest, bytes: Bytes): Unit =
    protocol_command_raw("Document.define_blob", List(Bytes(digest.toString), bytes))

  private def encode_command(
    resources: Resources,
    command: Command
  ) : (XML.Body, XML.Body, XML.Body, XML.Body, XML.Body, List[XML.Body]) = {
    import XML.Encode._

    val parents = command.theory_parents(resources).map(name => File.standard_url(name.node))
    val parents_xml: XML.Body = list(string)(parents)

    val blobs_xml: XML.Body = {
      val encode_blob: T[Exn.Result[Command.Blob]] =
        variant(List(
          { case Exn.Res(Command.Blob(a, b, c)) =>
              (Nil, triple(string, string, option(string))(
                (a.node, b.implode, c.map(p => p._1.toString)))) },
          { case Exn.Exn(e) => (Nil, string(Exn.message(e))) }))

      pair(list(encode_blob), int)(command.blobs, command.blobs_index)
    }

    val toks_xml: XML.Body = {
      val encode_tok: T[Token] = (tok => pair(int, int)((tok.kind.id, Symbol.length(tok.source))))
      list(encode_tok)(command.span.content)
    }
    val toks_sources_xml: List[XML.Body] = command.span.content.map(tok => XML.string(tok.source))

    (Document_ID.encode(command.id), XML.string(command.span.name),
      parents_xml, blobs_xml, toks_xml, toks_sources_xml)
  }

  def define_command(resources: Resources, command: Command): Unit = {
    val (a, b, c, d, e, rest) = encode_command(resources, command)
    protocol_command_args("Document.define_command", a :: b :: c :: d :: e :: rest)
  }

  def define_commands(resources: Resources, commands: List[Command]): Unit =
    protocol_command_args("Document.define_commands",
      commands.map { command =>
        import XML.Encode._
        val (a, b, c, d, e, rest) = encode_command(resources, command)
        pair(self, pair(self, pair(self, pair(self, pair(self, list(self))))))(
          a, (b, (c, (d, (e, rest)))))
      })

  def define_commands_bulk(resources: Resources, commands: List[Command]): Unit = {
    val (irregular, regular) = commands.partition(command => YXML.detect(command.source))
    irregular.foreach(define_command(resources, _))
    regular match {
      case Nil =>
      case List(command) => define_command(resources, command)
      case _ => define_commands(resources, regular)
    }
  }


  /* execution */

  def discontinue_execution(): Unit =
    protocol_command("Document.discontinue_execution")

  def cancel_exec(id: Document_ID.Exec): Unit =
    protocol_command("Document.cancel_exec", Document_ID.encode(id))


  /* document versions */

  def update(
    old_id: Document_ID.Version,
    new_id: Document_ID.Version,
    edits: List[Document.Edit_Command],
    consolidate: List[Document.Node.Name]
  ): Unit = {
    val consolidate_xml = { import XML.Encode._; list(string)(consolidate.map(_.node)) }
    val edits_xml = {
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
      edits.map({ case (name, edit) => pair(string, encode_edit(name))(name.node, edit) })
    }
    protocol_command_args("Document.update",
      Document_ID.encode(old_id) :: Document_ID.encode(new_id) :: consolidate_xml :: edits_xml)
  }

  def remove_versions(versions: List[Document.Version]): Unit =
    protocol_command("Document.remove_versions",
      XML.Encode.list(Document_ID.encode)(versions.map(_.id)))


  /* dialog via document content */

  def dialog_result(serial: Long, result: String): Unit =
    protocol_command("Document.dialog_result", XML.Encode.long(serial), XML.string(result))
}
