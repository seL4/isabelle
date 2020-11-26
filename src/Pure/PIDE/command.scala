/*  Title:      Pure/PIDE/command.scala
    Author:     Fabian Immler, TU Munich
    Author:     Makarius

Prover commands with accumulated results from execution.
*/

package isabelle


import scala.collection.mutable
import scala.collection.immutable.SortedMap


object Command
{
  type Edit = (Option[Command], Option[Command])

  type Blob = Exn.Result[(Document.Node.Name, Option[(SHA1.Digest, Symbol.Text_Chunk)])]
  type Blobs_Info = (List[Blob], Int)
  val no_blobs: Blobs_Info = (Nil, -1)


  /** accumulated results from prover **/

  /* results */

  object Results
  {
    type Entry = (Long, XML.Tree)
    val empty: Results = new Results(SortedMap.empty)
    def make(args: TraversableOnce[Results.Entry]): Results = (empty /: args)(_ + _)
    def merge(args: TraversableOnce[Results]): Results = (empty /: args)(_ ++ _)


    /* XML data representation */

    val encode: XML.Encode.T[Results] = (results: Results) =>
    { import XML.Encode._; list(pair(long, tree))(results.rep.toList) }

    val decode: XML.Decode.T[Results] = (body: XML.Body) =>
    { import XML.Decode._; make(list(pair(long, tree))(body)) }
  }

  final class Results private(private val rep: SortedMap[Long, XML.Tree])
  {
    def is_empty: Boolean = rep.isEmpty
    def defined(serial: Long): Boolean = rep.isDefinedAt(serial)
    def get(serial: Long): Option[XML.Tree] = rep.get(serial)
    def iterator: Iterator[Results.Entry] = rep.iterator

    def + (entry: Results.Entry): Results =
      if (defined(entry._1)) this
      else new Results(rep + entry)

    def ++ (other: Results): Results =
      if (this eq other) this
      else if (rep.isEmpty) other
      else (this /: other.iterator)(_ + _)

    override def hashCode: Int = rep.hashCode
    override def equals(that: Any): Boolean =
      that match {
        case other: Results => rep == other.rep
        case _ => false
      }
    override def toString: String = iterator.mkString("Results(", ", ", ")")
  }


  /* exports */

  object Exports
  {
    type Entry = (Long, Export.Entry)
    val empty: Exports = new Exports(SortedMap.empty)
    def merge(args: TraversableOnce[Exports]): Exports = (empty /: args)(_ ++ _)
  }

  final class Exports private(private val rep: SortedMap[Long, Export.Entry])
  {
    def is_empty: Boolean = rep.isEmpty
    def iterator: Iterator[Exports.Entry] = rep.iterator

    def + (entry: Exports.Entry): Exports =
      if (rep.isDefinedAt(entry._1)) this
      else new Exports(rep + entry)

    def ++ (other: Exports): Exports =
      if (this eq other) this
      else if (rep.isEmpty) other
      else (this /: other.iterator)(_ + _)

    override def hashCode: Int = rep.hashCode
    override def equals(that: Any): Boolean =
      that match {
        case other: Exports => rep == other.rep
        case _ => false
      }
    override def toString: String = iterator.mkString("Exports(", ", ", ")")
  }


  /* markups */

  object Markup_Index
  {
    val markup: Markup_Index = Markup_Index(false, Symbol.Text_Chunk.Default)
  }

  sealed case class Markup_Index(status: Boolean, chunk_name: Symbol.Text_Chunk.Name)

  object Markups
  {
    val empty: Markups = new Markups(Map.empty)
    def init(markup: Markup_Tree): Markups = new Markups(Map(Markup_Index.markup -> markup))
    def merge(args: TraversableOnce[Markups]): Markups = (empty /: args)(_ ++ _)


    /* XML data representation */

    def encode(source_length: Int): XML.Encode.T[Markups] = (markups: Markups) =>
    {
      import XML.Encode._

      val markup_index: T[Markup_Index] = (index: Markup_Index) =>
        pair(bool, Symbol.Text_Chunk.encode_name)(index.status, index.chunk_name)

      val markup_tree: T[Markup_Tree] =
        _.to_XML(Text.Range(0, source_length), Symbol.spaces(source_length), Markup.Elements.full)

      list(pair(markup_index, markup_tree))(markups.rep.toList)
    }

    val decode: XML.Decode.T[Markups] = (body: XML.Body) =>
    {
      import XML.Decode._

      val markup_index: T[Markup_Index] = (body: XML.Body) =>
      {
        val (status, chunk_name) = pair(bool, Symbol.Text_Chunk.decode_name)(body)
        Markup_Index(status, chunk_name)
      }

      (Markups.empty /: list(pair(markup_index, Markup_Tree.from_XML))(body))(_ + _)
    }
  }

  final class Markups private(private val rep: Map[Markup_Index, Markup_Tree])
  {
    def is_empty: Boolean = rep.isEmpty

    def apply(index: Markup_Index): Markup_Tree =
      rep.getOrElse(index, Markup_Tree.empty)

    def add(index: Markup_Index, markup: Text.Markup): Markups =
      new Markups(rep + (index -> (this(index) + markup)))

    def + (entry: (Markup_Index, Markup_Tree)): Markups =
    {
      val (index, tree) = entry
      new Markups(rep + (index -> (this(index).merge(tree, Text.Range.full, Markup.Elements.full))))
    }

    def ++ (other: Markups): Markups =
      if (this eq other) this
      else if (rep.isEmpty) other
      else (this /: other.rep.iterator)(_ + _)

    def redirection_iterator: Iterator[Document_ID.Generic] =
      for (Markup_Index(_, Symbol.Text_Chunk.Id(id)) <- rep.keysIterator)
        yield id

    def redirect(other_id: Document_ID.Generic): Markups =
    {
      val rep1 =
        (for {
          (Markup_Index(status, Symbol.Text_Chunk.Id(id)), markup) <- rep.iterator
          if other_id == id
        } yield (Markup_Index(status, Symbol.Text_Chunk.Default), markup)).toMap
      if (rep1.isEmpty) Markups.empty else new Markups(rep1)
    }

    override def hashCode: Int = rep.hashCode
    override def equals(that: Any): Boolean =
      that match {
        case other: Markups => rep == other.rep
        case _ => false
      }
    override def toString: String = rep.iterator.mkString("Markups(", ", ", ")")
  }


  /* state */

  object State
  {
    def get_result(states: List[State], serial: Long): Option[XML.Tree] =
      states.find(st => st.results.defined(serial)).map(st => st.results.get(serial).get)

    def get_result_proper(states: List[State], props: Properties.T): Option[Results.Entry] =
      for {
        serial <- Markup.Serial.unapply(props)
        tree @ XML.Elem(_, body) <- get_result(states, serial)
        if body.nonEmpty
      } yield (serial -> tree)

    def merge_results(states: List[State]): Results =
      Results.merge(states.map(_.results))

    def merge_exports(states: List[State]): Exports =
      Exports.merge(states.map(_.exports))

    def merge_markups(states: List[State]): Markups =
      Markups.merge(states.map(_.markups))

    def merge_markup(states: List[State], index: Markup_Index,
        range: Text.Range, elements: Markup.Elements): Markup_Tree =
      Markup_Tree.merge(states.map(_.markup(index)), range, elements)

    def merge(command: Command, states: List[State]): State =
      State(command, states.flatMap(_.status), merge_results(states),
        merge_exports(states), merge_markups(states))


    /* XML data representation */

    val encode: XML.Encode.T[State] = (st: State) =>
    {
      import XML.Encode._

      val command = st.command
      val blobs_names = command.blobs_names.map(_.node)
      val blobs_index = command.blobs_index
      require(command.blobs_ok)

      pair(long, pair(string, pair(pair(list(string), int), pair(Command_Span.encode,
          pair(list(Markup.encode), pair(Results.encode, Markups.encode(command.source.length)))))))(
        (command.id, (command.node_name.node, ((blobs_names, blobs_index), (command.span,
          (st.status, (st.results, st.markups)))))))
    }

    def decode(node_name: String => Document.Node.Name): XML.Decode.T[State] = (body: XML.Body) =>
    {
      import XML.Decode._
      val (id, (node, ((blobs_names, blobs_index), (span, (status, (results, markups)))))) =
        pair(long, pair(string, pair(pair(list(string), int), pair(Command_Span.decode,
          pair(list(Markup.decode), pair(Results.decode, Markups.decode))))))(body)

      val blobs_info: Blobs_Info =
        (blobs_names.map(name => Exn.Res((node_name(name), None)): Blob), blobs_index)
      val command = Command(id, node_name(node), blobs_info, span)
      State(command, status, results, Exports.empty, markups)
    }
  }

  sealed case class State(
    command: Command,
    status: List[Markup] = Nil,
    results: Results = Results.empty,
    exports: Exports = Exports.empty,
    markups: Markups = Markups.empty)
  {
    def initialized: Boolean = status.exists(markup => markup.name == Markup.INITIALIZED)
    def consolidating: Boolean = status.exists(markup => markup.name == Markup.CONSOLIDATING)
    def consolidated: Boolean = status.exists(markup => markup.name == Markup.CONSOLIDATED)

    lazy val maybe_consolidated: Boolean =
    {
      var touched = false
      var forks = 0
      var runs = 0
      for (markup <- status) {
        markup.name match {
          case Markup.FORKED => touched = true; forks += 1
          case Markup.JOINED => forks -= 1
          case Markup.RUNNING => touched = true; runs += 1
          case Markup.FINISHED => runs -= 1
          case _ =>
        }
      }
      touched && forks == 0 && runs == 0
    }

    lazy val document_status: Document_Status.Command_Status =
    {
      val warnings =
        if (results.iterator.exists(p => Protocol.is_warning(p._2) || Protocol.is_legacy(p._2)))
          List(Markup(Markup.WARNING, Nil))
        else Nil
      val errors =
        if (results.iterator.exists(p => Protocol.is_error(p._2)))
          List(Markup(Markup.ERROR, Nil))
        else Nil
      Document_Status.Command_Status.make((warnings ::: errors ::: status).iterator)
    }

    def markup(index: Markup_Index): Markup_Tree = markups(index)

    def redirect(other_command: Command): Option[State] =
    {
      val markups1 = markups.redirect(other_command.id)
      if (markups1.is_empty) None
      else Some(new State(other_command, markups = markups1))
    }

    private def add_status(st: Markup): State =
      copy(status = st :: status)

    private def add_result(entry: Results.Entry): State =
      copy(results = results + entry)

    def add_export(entry: Exports.Entry): Option[State] =
      if (command.node_name.theory == entry._2.theory_name) Some(copy(exports = exports + entry))
      else None

    private def add_markup(
      status: Boolean, chunk_name: Symbol.Text_Chunk.Name, m: Text.Markup): State =
    {
      val markups1 =
        if (status || Document_Status.Command_Status.liberal_elements(m.info.name))
          markups.add(Markup_Index(true, chunk_name), m)
        else markups
      copy(markups = markups1.add(Markup_Index(false, chunk_name), m))
    }

    def accumulate(
        self_id: Document_ID.Generic => Boolean,
        other_id: Document_ID.Generic => Option[(Symbol.Text_Chunk.Id, Symbol.Text_Chunk)],
        message: XML.Elem,
        xml_cache: XML.Cache): State =
      message match {
        case XML.Elem(Markup(Markup.STATUS, _), msgs) =>
          if (command.span.is_theory) this
          else {
            (this /: msgs)((state, msg) =>
              msg match {
                case elem @ XML.Elem(markup, Nil) =>
                  state.
                    add_status(markup).
                    add_markup(true, Symbol.Text_Chunk.Default, Text.Info(command.core_range, elem))
                case _ =>
                  Output.warning("Ignored status message: " + msg)
                  state
              })
          }

        case XML.Elem(Markup(Markup.REPORT, atts0), msgs) =>
          (this /: msgs)((state, msg) =>
            {
              def bad(): Unit = Output.warning("Ignored report message: " + msg)

              msg match {
                case XML.Elem(Markup(name, atts1), args) =>
                  val atts = atts1 ::: atts0
                  command.reported_position(atts) match {
                    case Some((id, chunk_name)) =>
                      val target =
                        if (self_id(id) && command.chunks.isDefinedAt(chunk_name))
                          Some((chunk_name, command.chunks(chunk_name)))
                        else if (chunk_name == Symbol.Text_Chunk.Default) other_id(id)
                        else None

                      (target, atts) match {
                        case (Some((target_name, target_chunk)), Position.Range(symbol_range)) =>
                          target_chunk.incorporate(symbol_range) match {
                            case Some(range) =>
                              val props = atts.filterNot(Markup.position_property)
                              val elem = xml_cache.elem(XML.Elem(Markup(name, props), args))
                              state.add_markup(false, target_name, Text.Info(range, elem))
                            case None => bad(); state
                          }
                        case _ =>
                          // silently ignore excessive reports
                          state
                      }

                    case _ => bad(); state
                  }
                case _ => bad(); state
              }
            })

        case XML.Elem(Markup(name, props), body) =>
          props match {
            case Markup.Serial(i) =>
              val markup_message =
                xml_cache.elem(XML.Elem(Markup(Markup.message(name), props), body))
              val message_markup =
                xml_cache.elem(XML.elem(Markup(name, props.filter(p => p._1 == Markup.SERIAL))))

              var st = add_result(i -> markup_message)
              if (Protocol.is_inlined(message)) {
                for {
                  (chunk_name, chunk) <- command.chunks.iterator
                  range <- command.message_positions(self_id, chunk_name, chunk, message)
                } st = st.add_markup(false, chunk_name, Text.Info(range, message_markup))
              }
              st

            case _ =>
              Output.warning("Ignored message without serial number: " + message)
              this
          }
      }
  }



  /** static content **/

  /* make commands */

  def apply(
    id: Document_ID.Command,
    node_name: Document.Node.Name,
    blobs_info: Blobs_Info,
    span: Command_Span.Span): Command =
  {
    val (source, span1) = span.compact_source
    new Command(id, node_name, blobs_info, span1, source, Results.empty, Markups.empty)
  }

  val empty: Command =
    Command(Document_ID.none, Document.Node.Name.empty, no_blobs, Command_Span.empty)

  def unparsed(
    source: String,
    theory: Boolean = false,
    id: Document_ID.Command = Document_ID.none,
    node_name: Document.Node.Name = Document.Node.Name.empty,
    results: Results = Results.empty,
    markups: Markups = Markups.empty): Command =
  {
    val (source1, span1) = Command_Span.unparsed(source, theory).compact_source
    new Command(id, node_name, no_blobs, span1, source1, results, markups)
  }

  def text(source: String): Command = unparsed(source)

  def rich_text(id: Document_ID.Command, results: Results, body: XML.Body): Command =
    unparsed(XML.content(body), id = id, results = results,
      markups = Markups.init(Markup_Tree.from_XML(body)))


  /* perspective */

  object Perspective
  {
    val empty: Perspective = Perspective(Nil)
  }

  sealed case class Perspective(commands: List[Command])  // visible commands in canonical order
  {
    def is_empty: Boolean = commands.isEmpty

    def same(that: Perspective): Boolean =
    {
      val cmds1 = this.commands
      val cmds2 = that.commands
      require(!cmds1.exists(_.is_undefined))
      require(!cmds2.exists(_.is_undefined))
      cmds1.length == cmds2.length &&
        (cmds1.iterator zip cmds2.iterator).forall({ case (c1, c2) => c1.id == c2.id })
    }
  }


  /* blobs: inlined errors and auxiliary files */

  private def clean_tokens(tokens: List[Token]): List[(Token, Int)] =
  {
    def clean(toks: List[(Token, Int)]): List[(Token, Int)] =
      toks match {
        case (t1, i1) :: (t2, i2) :: rest =>
          if (t1.is_keyword && t1.source == "%" && t2.is_name) clean(rest)
          else (t1, i1) :: clean((t2, i2) :: rest)
        case _ => toks
      }
    clean(tokens.zipWithIndex.filter({ case (t, _) => t.is_proper }))
  }

  private def find_file(tokens: List[(Token, Int)]): Option[(String, Int)] =
    if (tokens.exists({ case (t, _) => t.is_command })) {
      tokens.dropWhile({ case (t, _) => !t.is_command }).
        collectFirst({ case (t, i) if t.is_embedded => (t.content, i) })
    }
    else None

  def span_files(syntax: Outer_Syntax, span: Command_Span.Span): (List[String], Int) =
    syntax.load_command(span.name) match {
      case Some(exts) =>
        find_file(clean_tokens(span.content)) match {
          case Some((file, i)) =>
            if (exts.isEmpty) (List(file), i)
            else (exts.map(ext => file + "." + ext), i)
          case None => (Nil, -1)
        }
      case None => (Nil, -1)
    }

  def blobs_info(
    resources: Resources,
    syntax: Outer_Syntax,
    get_blob: Document.Node.Name => Option[Document.Blob],
    can_import: Document.Node.Name => Boolean,
    node_name: Document.Node.Name,
    span: Command_Span.Span): Blobs_Info =
  {
    span.name match {
      // inlined errors
      case Thy_Header.THEORY =>
        val reader = Scan.char_reader(Token.implode(span.content))
        val imports_pos = resources.check_thy_reader(node_name, reader).imports_pos
        val raw_imports =
          try {
            val read_imports = Thy_Header.read(reader, Token.Pos.none).imports
            if (imports_pos.length == read_imports.length) read_imports else error("")
          }
          catch { case exn: Throwable => List.fill(imports_pos.length)("") }

        val errors =
          for { ((import_name, pos), s) <- imports_pos zip raw_imports if !can_import(import_name) }
          yield {
            val completion =
              if (Thy_Header.is_base_name(s)) resources.complete_import_name(node_name, s) else Nil
            val msg =
              "Bad theory import " +
                Markup.Path(import_name.node).markup(quote(import_name.toString)) +
                Position.here(pos) + Completion.report_theories(pos, completion)
            Exn.Exn(ERROR(msg)): Command.Blob
          }
        (errors, -1)

      // auxiliary files
      case _ =>
        val (files, index) = span_files(syntax, span)
        val blobs =
          files.map(file =>
            (Exn.capture {
              val name = Document.Node.Name(resources.append(node_name, Path.explode(file)))
              val blob = get_blob(name).map(blob => ((blob.bytes.sha1_digest, blob.chunk)))
              (name, blob)
            }).user_error)
        (blobs, index)
    }
  }
}


final class Command private(
    val id: Document_ID.Command,
    val node_name: Document.Node.Name,
    val blobs_info: Command.Blobs_Info,
    val span: Command_Span.Span,
    val source: String,
    val init_results: Command.Results,
    val init_markups: Command.Markups)
{
  override def toString: String = id + "/" + span.kind.toString


  /* classification */

  def is_proper: Boolean = span.kind.isInstanceOf[Command_Span.Command_Span]
  def is_ignored: Boolean = span.kind == Command_Span.Ignored_Span

  def is_undefined: Boolean = id == Document_ID.none
  val is_unparsed: Boolean = span.content.exists(_.is_unparsed)
  val is_unfinished: Boolean = span.content.exists(_.is_unfinished)

  def potentially_initialized: Boolean = span.name == Thy_Header.THEORY


  /* blobs */

  def blobs: List[Command.Blob] = blobs_info._1
  def blobs_index: Int = blobs_info._2

  def blobs_ok: Boolean =
    blobs.forall({ case Exn.Res(_) => true case _ => false })

  def blobs_names: List[Document.Node.Name] =
    for (Exn.Res((name, _)) <- blobs) yield name

  def blobs_undefined: List[Document.Node.Name] =
    for (Exn.Res((name, None)) <- blobs) yield name

  def blobs_defined: List[(Document.Node.Name, SHA1.Digest)] =
    for (Exn.Res((name, Some((digest, _)))) <- blobs) yield (name, digest)

  def blobs_changed(doc_blobs: Document.Blobs): Boolean =
    blobs.exists({ case Exn.Res((name, _)) => doc_blobs.changed(name) case _ => false })


  /* source chunks */

  val chunk: Symbol.Text_Chunk = Symbol.Text_Chunk(source)

  val chunks: Map[Symbol.Text_Chunk.Name, Symbol.Text_Chunk] =
    ((Symbol.Text_Chunk.Default -> chunk) ::
      (for (Exn.Res((name, Some((_, file)))) <- blobs)
        yield Symbol.Text_Chunk.File(name.node) -> file)).toMap

  def length: Int = source.length
  def range: Text.Range = chunk.range

  val core_range: Text.Range =
    Text.Range(0,
      (length /: span.content.reverse.iterator.takeWhile(_.is_ignored))(_ - _.source.length))

  def source(range: Text.Range): String = range.substring(source)


  /* reported positions */

  def reported_position(pos: Position.T): Option[(Document_ID.Generic, Symbol.Text_Chunk.Name)] =
    pos match {
      case Position.Id(id) =>
        val chunk_name =
          pos match {
            case Position.File(name) if name != node_name.node =>
              Symbol.Text_Chunk.File(name)
            case _ => Symbol.Text_Chunk.Default
          }
        Some((id, chunk_name))
      case _ => None
    }

  def message_positions(
    self_id: Document_ID.Generic => Boolean,
    chunk_name: Symbol.Text_Chunk.Name,
    chunk: Symbol.Text_Chunk,
    message: XML.Elem): Set[Text.Range] =
  {
    def elem(props: Properties.T, set: Set[Text.Range]): Set[Text.Range] =
      reported_position(props) match {
        case Some((id, name)) if self_id(id) && name == chunk_name =>
          val opt_range =
            Position.Range.unapply(props) orElse {
              if (name == Symbol.Text_Chunk.Default)
                Position.Range.unapply(span.position)
              else None
            }
          opt_range match {
            case Some(symbol_range) =>
              chunk.incorporate(symbol_range) match {
                case Some(range) => set + range
                case _ => set
              }
            case None => set
          }
        case _ => set
      }
    def tree(set: Set[Text.Range], t: XML.Tree): Set[Text.Range] =
      t match {
        case XML.Wrapped_Elem(Markup(name, props), _, body) =>
          body.foldLeft(if (Rendering.position_elements(name)) elem(props, set) else set)(tree)
        case XML.Elem(Markup(name, props), body) =>
          body.foldLeft(if (Rendering.position_elements(name)) elem(props, set) else set)(tree)
        case XML.Text(_) => set
      }

    val set = tree(Set.empty, message)
    if (set.isEmpty) elem(message.markup.properties, set)
    else set
  }


  /* accumulated results */

  val init_state: Command.State =
    Command.State(this, results = init_results, markups = init_markups)

  val empty_state: Command.State = Command.State(this)
}
