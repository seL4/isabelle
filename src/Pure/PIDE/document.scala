/*  Title:      Pure/PIDE/document.scala
    Author:     Makarius

Document as collection of named nodes, each consisting of an editable
list of commands, associated with asynchronous execution process.
*/

package isabelle


import scala.collection.mutable


object Document {
  /** document structure **/

  /* overlays -- print functions with arguments */

  object Overlays {
    val empty = new Overlays(Map.empty)
  }

  final class Overlays private(rep: Map[Node.Name, Node.Overlays]) {
    def apply(name: Node.Name): Node.Overlays =
      rep.getOrElse(name, Node.Overlays.empty)

    private def update(name: Node.Name, f: Node.Overlays => Node.Overlays): Overlays = {
      val node_overlays = f(apply(name))
      new Overlays(if (node_overlays.is_empty) rep - name else rep + (name -> node_overlays))
    }

    def insert(command: Command, fn: String, args: List[String]): Overlays =
      update(command.node_name, _.insert(command, fn, args))

    def remove(command: Command, fn: String, args: List[String]): Overlays =
      update(command.node_name, _.remove(command, fn, args))

    override def toString: String = rep.mkString("Overlays(", ",", ")")
  }


  /* document blobs: auxiliary files */

  object Blobs {
    sealed case class Item(
      bytes: Bytes,
      source: String,
      chunk: Symbol.Text_Chunk,
      changed: Boolean
    ) {
      def source_wellformed: Boolean = bytes.wellformed_text.nonEmpty
      def unchanged: Item = copy(changed = false)
    }

    def apply(blobs: Map[Node.Name, Item]): Blobs = new Blobs(blobs)
    val empty: Blobs = apply(Map.empty)

    def make(blobs: List[(Command.Blob, Item)]): Blobs =
      if (blobs.isEmpty) empty
      else apply((for ((a, b) <- blobs.iterator) yield a.name -> b).toMap)
  }

  final class Blobs private(blobs: Map[Node.Name, Blobs.Item]) {
    def get(name: Node.Name): Option[Blobs.Item] = blobs.get(name)

    def changed(name: Node.Name): Boolean =
      get(name) match {
        case Some(blob) => blob.changed
        case None => false
      }

    override def toString: String = blobs.mkString("Blobs(", ",", ")")
  }


  /* document nodes: theories and auxiliary files */

  type Edit[A, B] = (Node.Name, Node.Edit[A, B])
  type Edit_Text = Edit[Text.Edit, Text.Perspective]
  type Edit_Command = Edit[Command.Edit, Command.Perspective]

  object Node {
    /* header and name */

    sealed case class Header(
      imports_pos: List[(Name, Position.T)] = Nil,
      keywords: Thy_Header.Keywords = Nil,
      abbrevs: Thy_Header.Abbrevs = Nil,
      errors: List[String] = Nil
    ) {
      def imports: List[Name] = imports_pos.map(_._1)

      def append_errors(msgs: List[String]): Header =
        copy(errors = errors ::: msgs)

      def cat_errors(msg2: String): Header =
        copy(errors = errors.map(msg1 => Exn.cat_message(msg1, msg2)))
    }

    val no_header: Header = Header()
    def bad_header(msg: String): Header = Header(errors = List(msg))

    object Name {
      def apply(node: String, theory: String = ""): Name = new Name(node, theory)

      def loaded_theory(theory: String): Name = Name(theory, theory = theory)

      val empty: Name = Name("")

      object Ordering extends scala.math.Ordering[Name] {
        def compare(name1: Name, name2: Name): Int = name1.node compare name2.node
      }

      type Graph[A] = isabelle.Graph[Node.Name, A]

      def make_graph[A](entries: List[((Name, A), List[Name])]): Graph[A] =
        Graph.make(entries, converse = true)(Ordering)
    }

    final class Name private(val node: String, val theory: String) {
      override def hashCode: Int = node.hashCode
      override def equals(that: Any): Boolean =
        that match {
          case other: Name => node == other.node
          case _ => false
        }

      def file_name: String = Url.get_base_name(node).getOrElse("")

      def path: Path = Path.explode(File.standard_path(node))

      def master_dir: String = Url.strip_base_name(node).getOrElse("")

      def is_theory: Boolean = theory.nonEmpty

      def theory_base_name: String = Long_Name.base_name(theory)

      override def toString: String = if (is_theory) theory else node

      def json: JSON.Object.T =
        JSON.Object("node_name" -> node, "theory_name" -> theory)
    }

    sealed case class Entry(name: Node.Name, header: Node.Header) {
      override def toString: String = name.toString
    }


    /* node overlays */

    object Overlays {
      val empty = new Overlays(Multi_Map.empty)
    }

    final class Overlays private(rep: Multi_Map[Command, (String, List[String])]) {
      def commands: Set[Command] = rep.keySet
      def is_empty: Boolean = rep.isEmpty
      def dest: List[(Command, (String, List[String]))] = rep.iterator.toList
      def insert(cmd: Command, fn: String, args: List[String]): Overlays =
        new Overlays(rep.insert(cmd, (fn, args)))
      def remove(cmd: Command, fn: String, args: List[String]): Overlays =
        new Overlays(rep.remove(cmd, (fn, args)))

      override def toString: String = rep.mkString("Node.Overlays(", ",", ")")
    }


    /* edits */

    sealed abstract class Edit[A, B] {
      def foreach(f: A => Unit): Unit = {
        this match {
          case Edits(es) => es.foreach(f)
          case _ =>
        }
      }

      def is_void: Boolean =
        this match {
          case Edits(Nil) => true
          case _ => false
        }
    }
    case class Blob[A, B](blob: Blobs.Item) extends Edit[A, B]

    case class Edits[A, B](edits: List[A]) extends Edit[A, B]
    case class Deps[A, B](header: Header) extends Edit[A, B]
    case class Perspective[A, B](required: Boolean, visible: B, overlays: Overlays) extends Edit[A, B]


    /* perspective */

    object Perspective_Text {
      type T = Perspective[Text.Edit, Text.Perspective]
      val empty: T = Perspective(false, Text.Perspective.empty, Overlays.empty)
      def is_empty(perspective: T): Boolean =
        !perspective.required &&
        perspective.visible.is_empty &&
        perspective.overlays.is_empty
    }

    object Perspective_Command {
      type T = Perspective[Command.Edit, Command.Perspective]
      val empty: T = Perspective(false, Command.Perspective.empty, Overlays.empty)
      def is_empty(perspective: T): Boolean =
        !perspective.required &&
        perspective.visible.is_empty &&
        perspective.overlays.is_empty
    }


    /* commands */

    object Commands {
      def apply(commands: Linear_Set[Command]): Commands = new Commands(commands)
      val empty: Commands = apply(Linear_Set.empty)

      def starts(
        commands: Iterator[Command],
        init: Int = 0,
        count: Command => Int = _.length
      ) : Iterator[(Command, Int)] = {
        var i = init
        for (command <- commands) yield {
          val start = i
          i += count(command)
          (command, start)
        }
      }

      def starts_pos(
        commands: Iterator[Command],
        pos: Token.Pos = Token.Pos.start
      ) : Iterator[(Command, Token.Pos)] = {
        var p = pos
        for (command <- commands) yield {
          val start = p
          p = command.span.content.foldLeft(p)(_.advance(_))
          (command, start)
        }
      }

      private val block_size = 256
    }

    final class Commands private(val commands: Linear_Set[Command]) {
      lazy val start_lines: Map[Document_ID.Command, Int] =
        (for {
          (command, line) <-
            Node.Commands.starts(commands.iterator, init = 1,
              count = cmd => Library.count_newlines(cmd.source))
        } yield command.id -> line).toMap

      lazy val load_commands: List[Command] =
        commands.iterator.filter(cmd => cmd.blobs.nonEmpty).toList

      private lazy val full_index: (Array[(Command, Text.Offset)], Text.Range) = {
        val blocks = new mutable.ListBuffer[(Command, Text.Offset)]
        var next_block = 0
        var last_stop = 0
        for ((command, start) <- Commands.starts(commands.iterator)) {
          last_stop = start + command.length
          while (last_stop + 1 > next_block) {
            blocks += (command -> start)
            next_block += Commands.block_size
          }
        }
        (blocks.toArray, Text.Range(0, last_stop))
      }

      private def full_range: Text.Range = full_index._2

      def iterator(i: Text.Offset = 0): Iterator[(Command, Text.Offset)] = {
        if (commands.nonEmpty && full_range.contains(i)) {
          val (cmd0, start0) = full_index._1(i / Commands.block_size)
          Node.Commands.starts(commands.iterator(cmd0), start0) dropWhile {
            case (cmd, start) => start + cmd.length <= i }
        }
        else Iterator.empty
      }
    }

    val empty: Node = new Node()

    def init_blob(blob: Blobs.Item): Node =
      new Node(get_blob = Some(blob.unchanged))
  }

  final class Node private(
    val get_blob: Option[Blobs.Item] = None,
    val header: Node.Header = Node.no_header,
    val syntax: Option[Outer_Syntax] = None,
    val text_perspective: Text.Perspective = Text.Perspective.empty,
    val perspective: Node.Perspective_Command.T = Node.Perspective_Command.empty,
    _commands: Node.Commands = Node.Commands.empty
  ) {
    def is_empty: Boolean =
      get_blob.isEmpty &&
      header == Node.no_header &&
      text_perspective.is_empty &&
      Node.Perspective_Command.is_empty(perspective) &&
      commands.isEmpty

    def has_header: Boolean = header != Node.no_header

    override def toString: String =
      if (is_empty) "empty"
      else if (get_blob.isDefined) "blob"
      else "node"

    def commands: Linear_Set[Command] = _commands.commands
    def command_start_line(command: Command): Option[Int] =
      _commands.start_lines.get(command.id)
    def load_commands: List[Command] = _commands.load_commands
    def load_commands_changed(doc_blobs: Blobs): Boolean =
      load_commands.exists(_.blobs_changed(doc_blobs))

    def update_header(new_header: Node.Header): Node =
      new Node(get_blob, new_header, syntax, text_perspective, perspective, _commands)

    def update_syntax(new_syntax: Option[Outer_Syntax]): Node =
      new Node(get_blob, header, new_syntax, text_perspective, perspective, _commands)

    def update_perspective(
        new_text_perspective: Text.Perspective,
        new_perspective: Node.Perspective_Command.T): Node =
      new Node(get_blob, header, syntax, new_text_perspective, new_perspective, _commands)

    def edit_perspective: Node.Edit[Text.Edit, Text.Perspective] =
      Node.Perspective(perspective.required, text_perspective, perspective.overlays)

    def same_perspective(
        other_text_perspective: Text.Perspective,
        other_perspective: Node.Perspective_Command.T): Boolean =
      text_perspective == other_text_perspective &&
      perspective.required == other_perspective.required &&
      perspective.visible.same(other_perspective.visible) &&
      perspective.overlays == other_perspective.overlays

    def update_commands(new_commands: Linear_Set[Command]): Node =
      if (new_commands eq _commands.commands) this
      else {
        new Node(get_blob, header, syntax, text_perspective, perspective,
          Node.Commands(new_commands))
      }

    def command_iterator(i: Text.Offset = 0): Iterator[(Command, Text.Offset)] =
      _commands.iterator(i)

    def command_iterator(range: Text.Range): Iterator[(Command, Text.Offset)] =
      command_iterator(range.start) takeWhile { case (_, start) => start < range.stop }

    def command_start(cmd: Command): Option[Text.Offset] =
      Node.Commands.starts(commands.iterator).find(_._1 == cmd).map(_._2)

    lazy val source_wellformed: Boolean =
      get_blob match {
        case Some(blob) => blob.source_wellformed
        case None => true
      }

    lazy val source: String =
      get_blob match {
        case Some(blob) => blob.source
        case None => command_iterator().map({ case (cmd, _) => cmd.source }).mkString
      }
  }


  /* development graph */

  object Nodes {
    val empty: Nodes = new Nodes(Graph.empty(Node.Name.Ordering))

    private def init(graph: Graph[Node.Name, Node], name: Node.Name): Graph[Node.Name, Node] =
      graph.default_node(name, Node.empty)
  }

  final class Nodes private(graph: Graph[Node.Name, Node]) {
    def apply(name: Node.Name): Node = Nodes.init(graph, name).get_node(name)

    def is_suppressed(name: Node.Name): Boolean = {
      val graph1 = Nodes.init(graph, name)
      graph1.is_maximal(name) && graph1.get_node(name).is_empty
    }

    def purge_suppressed: Option[Nodes] =
      graph.keys_iterator.filter(is_suppressed).toList match {
        case Nil => None
        case del => Some(new Nodes(del.foldLeft(graph)(_.del_node(_))))
      }

    def + (entry: (Node.Name, Node)): Nodes = {
      val (name, node) = entry
      val imports = node.header.imports
      val graph1 = (name :: imports).foldLeft(graph)(Nodes.init)
      val graph2 =
        graph1.imm_preds(name).foldLeft(graph1) { case (g, dep) => g.del_edge(dep, name) }
      val graph3 = imports.foldLeft(graph2) { case (g, dep) => g.add_edge(dep, name) }
      new Nodes(graph3.map_node(name, _ => node))
    }

    def domain: Set[Node.Name] = graph.domain

    def iterator: Iterator[(Node.Name, Node)] =
      graph.iterator.map({ case (name, (node, _)) => (name, node) })

    def theory_name(theory: String): Option[Node.Name] =
      graph.keys_iterator.find(name => name.theory == theory)

    def commands_loading(file_name: Node.Name): List[Command] =
      (for {
        (_, node) <- iterator
        cmd <- node.load_commands.iterator
        name <- cmd.blobs_names.iterator
        if name == file_name
      } yield cmd).toList

    def descendants(names: List[Node.Name]): List[Node.Name] =
      names.foldLeft(graph)(Nodes.init).all_succs(names)
    def topological_order: List[Node.Name] = graph.topological_order

    override def toString: String = topological_order.mkString("Nodes(", ",", ")")
  }



  /** versioning **/

  /* particular document versions */

  object Version {
    val init: Version = new Version()
    def make(nodes: Nodes): Version = new Version(Document_ID.make(), nodes)

    def purge_future(
      versions: Map[Document_ID.Version, Version],
      future: Future[Version]
    ) : Future[Version] = {
      if (future.is_finished) {
        val version = future.join
        versions.get(version.id) match {
          case Some(version1) if !(version eq version1) => Future.value(version1)
          case _ => future
        }
      }
      else future
    }

    def purge_suppressed(
      versions: Map[Document_ID.Version, Version]
    ): Map[Document_ID.Version, Version] = {
      (for ((id, v) <- versions.iterator; v1 <- v.purge_suppressed) yield (id, v1)).
        foldLeft(versions)(_ + _)
    }
  }

  final class Version private(
    val id: Document_ID.Version = Document_ID.none,
    val nodes: Nodes = Nodes.empty
  ) {
    override def toString: String = "Version(" + id + ")"

    def purge_suppressed: Option[Version] =
      nodes.purge_suppressed.map(new Version(id, _))
  }


  /* changes of plain text, eventually resulting in document edits */

  object Change {
    val init: Change = new Change()

    def make(previous: Future[Version], edits: List[Edit_Text], version: Future[Version]): Change =
      new Change(Some(previous), edits.reverse, version)
  }

  final class Change private(
    val previous: Option[Future[Version]] = Some(Future.value(Version.init)),
    val rev_edits: List[Edit_Text] = Nil,
    val version: Future[Version] = Future.value(Version.init)
  ) {
    def is_finished: Boolean =
      (previous match { case None => true case Some(future) => future.is_finished }) &&
      version.is_finished

    def truncate: Change = new Change(None, Nil, version)

    def purge(versions: Map[Document_ID.Version, Version]): Option[Change] = {
      val previous1 = previous.map(Version.purge_future(versions, _))
      val version1 = Version.purge_future(versions, version)
      if ((previous eq previous1) && (version eq version1)) None
      else Some(new Change(previous1, rev_edits, version1))
    }
  }


  /* history navigation */

  object History {
    val init: History = new History()
  }

  final class History private(
    val undo_list: List[Change] = List(Change.init)  // non-empty list
  ) {
    override def toString: String = "History(" + undo_list.length + ")"

    def tip: Change = undo_list.head
    def + (change: Change): History = new History(change :: undo_list)

    def prune(check: Change => Boolean, retain: Int): Option[(List[Change], History)] = {
      val n = undo_list.iterator.zipWithIndex.find(p => check(p._1)).get._2 + 1
      val (retained, dropped) = undo_list.splitAt(n max retain)

      retained.splitAt(retained.length - 1) match {
        case (prefix, List(last)) => Some(dropped, new History(prefix ::: List(last.truncate)))
        case _ => None
      }
    }

    def purge(versions: Map[Document_ID.Version, Version]): History = {
      val undo_list1 = undo_list.map(_.purge(versions))
      if (undo_list1.forall(_.isEmpty)) this
      else new History(for ((a, b) <- undo_list1 zip undo_list) yield a.getOrElse(b))
    }
  }


  /* snapshot: persistent user-view of document state */

  object Pending_Edits {
    val empty: Pending_Edits = make(Nil)

    def make(models: Iterable[Model]): Pending_Edits =
      new Pending_Edits(
        (for {
          model <- models.iterator
          edits = model.pending_edits if edits.nonEmpty
        } yield model.node_name -> edits).toMap)
  }

  final class Pending_Edits(pending_edits: Map[Node.Name, List[Text.Edit]]) {
    def is_stable: Boolean = pending_edits.isEmpty

    def + (entry: (Node.Name, List[Text.Edit])): Pending_Edits = {
      val (name, es) = entry
      if (es.isEmpty) this
      else new Pending_Edits(pending_edits + (name -> (es ::: edits(name))))
    }

    def edits(name: Node.Name): List[Text.Edit] =
      pending_edits.getOrElse(name, Nil)

    def reverse_edits(name: Node.Name): List[Text.Edit] =
      reverse_pending_edits.getOrElse(name, Nil)

    private lazy val reverse_pending_edits =
      (for ((name, es) <- pending_edits.iterator) yield (name, es.reverse)).toMap
  }

  object Snapshot {
    val init: Snapshot = State.init.snapshot()
  }

  class Snapshot private[Document](
    val state: State,
    val version: Version,
    val node_name: Node.Name,
    pending_edits: Pending_Edits,
    val snippet_commands: List[Command]
  ) {
    override def toString: String =
      "Snapshot(node = " + node_name.node + ", version = " + version.id +
        (if (is_outdated) ", outdated" else "") + ")"

    def switch(name: Node.Name): Snapshot =
      if (name == node_name) this
      else new Snapshot(state, version, name, pending_edits, Nil)


    /* nodes */

    def get_node(name: Node.Name): Node = version.nodes(name)

    val node: Node = get_node(node_name)

    def node_files: List[Node.Name] =
      node_name :: node.load_commands.flatMap(_.blobs_names)

    def node_consolidated(name: Node.Name): Boolean =
      state.node_consolidated(version, name)

    def theory_consolidated(theory: String): Boolean =
      version.nodes.theory_name(theory) match {
        case Some(name) => node_consolidated(name)
        case None => false
      }


    /* pending edits */

    def is_outdated: Boolean = !pending_edits.is_stable

    def convert(offset: Text.Offset): Text.Offset =
      pending_edits.edits(node_name).foldLeft(offset) { case (i, edit) => edit.convert(i) }
    def revert(offset: Text.Offset): Text.Offset =
      pending_edits.reverse_edits(node_name).foldLeft(offset) { case (i, edit) => edit.revert(i) }

    def convert(range: Text.Range): Text.Range = range.map(convert)
    def revert(range: Text.Range): Text.Range = range.map(revert)


    /* theory load commands */

    val commands_loading: List[Command] =
      if (node_name.is_theory) Nil
      else version.nodes.commands_loading(node_name)

    def commands_loading_ranges(pred: Node.Name => Boolean): List[Text.Range] =
      (for {
        cmd <- node.load_commands.iterator
        blob_name <- cmd.blobs_names.iterator
        if pred(blob_name)
        start <- node.command_start(cmd)
      } yield convert(cmd.core_range + start)).toList


    /* command as add-on snippet */

    def snippet(commands: List[Command], doc_blobs: Blobs): Snapshot = {
      require(commands.nonEmpty, "no snippet commands")

      val node_name = commands.head.node_name
      val node_commands = Linear_Set.from(commands)

      require(commands.forall(command => command.node_name == node_name),
        "incoherent snippet node names")

      val blobs =
        for {
          command <- commands
          a <- command.blobs_names
          b <- doc_blobs.get(a)
        } yield a -> b

      val nodes0 = version.nodes
      val nodes1 = nodes0 + (node_name -> nodes0(node_name).update_commands(node_commands))
      val nodes2 = blobs.foldLeft(nodes1) { case (ns, (a, b)) => ns + (a -> Node.init_blob(b)) }
      val version1 = Version.make(nodes2)

      val edits: List[Edit_Text] =
        List(node_name -> Node.Edits(List(Text.Edit.insert(0, Command.full_source(commands))))) :::
        blobs.map({ case (a, b) => a -> Node.Blob(b) })

      val assign_update: Assign_Update =
        commands.map(command => command.id -> List(Document_ID.make()))

      val state0 = commands.foldLeft(state)(_.define_command(_))
      val state1 =
        state0.continue_history(Future.value(version), edits, Future.value(version1))
          .define_version(version1, state0.the_assignment(version))
          .assign(version1.id, Nil, assign_update)._2

      state1.snapshot(node_name = node_name, snippet_commands = commands)
    }


    /* markup and messages */

    def xml_markup(
        range: Text.Range = Text.Range.full,
        elements: Markup.Elements = Markup.Elements.full): XML.Body =
      state.xml_markup(version, node_name, range = range, elements = elements)

    lazy val messages: List[(XML.Elem, Position.T)] =
      (for {
        (command, start) <-
          Node.Commands.starts_pos(node.commands.iterator, Token.Pos.file(node_name.node))
        pos = command.span.keyword_pos(start).position(command.span.name)
        (_, elem) <- state.command_results(version, command).iterator
       } yield (elem, pos)).toList


    /* exports */

    lazy val exports: List[Export.Entry] =
      state.node_exports(version, node_name).iterator.map(_._2).toList

    lazy val all_exports: Map[Export.Entry_Name, Export.Entry] =
      (for {
        (name, _) <- version.nodes.iterator
        (_, entry) <- state.node_exports(version, name).iterator
        if entry.entry_name.session == Sessions.DRAFT
      } yield entry.entry_name -> entry).toMap


    /* find command */

    def find_command(id: Document_ID.Generic): Option[(Node, Command)] =
      state.lookup_id(id) match {
        case None => None
        case Some(st) =>
          val command = st.command
          val command_node = get_node(command.node_name)
          if (command_node.commands.contains(command)) Some((command_node, command)) else None
      }

    def find_command_position(
      id: Document_ID.Generic,
      offset: Symbol.Offset
    ): Option[Line.Node_Position] = {
      for ((node, command) <- find_command(id))
      yield {
        val name = command.node_name.node
        val sources_iterator =
          node.commands.iterator.takeWhile(_ != command).map(_.source) ++
            (if (offset == 0) Iterator.empty
             else Iterator.single(command.source(Text.Range(0, command.chunk.decode(offset)))))
        val pos = sources_iterator.foldLeft(Line.Position.zero)(_.advance(_))
        Line.Node_Position(name, pos)
      }
    }

    def find_command_line(id: Document_ID.Generic, offset: Symbol.Offset): Option[Int] =
      for {
        (node, command) <- find_command(id)
        range = Text.Range(0, command.chunk.decode(offset))
        text <- range.try_substring(command.source)
        line <- node.command_start_line(command)
      } yield line + Library.count_newlines(text)

    def current_command(other_node_name: Node.Name, offset: Text.Offset): Option[Command] =
      if (other_node_name.is_theory) {
        val other_node = get_node(other_node_name)
        val iterator = other_node.command_iterator(revert(offset) max 0)
        if (iterator.hasNext) {
          val (command0, _) = iterator.next()
          other_node.commands.reverse.iterator(command0).find(command => !command.is_ignored)
        }
        else other_node.commands.reverse.iterator.find(command => !command.is_ignored)
      }
      else version.nodes.commands_loading(other_node_name).headOption


    /* command results */

    def command_results(range: Text.Range): Command.Results =
      Command.State.merge_results(
        select[List[Command.State]](range, Markup.Elements.full,
          command_states => _ => Some(command_states)).flatMap(_.info))

    def command_results(command: Command): Command.Results =
      state.command_results(version, command)


    /* cumulate markup */

    def cumulate[A](
      range: Text.Range,
      info: A,
      elements: Markup.Elements,
      result: List[Command.State] => (A, Text.Markup) => Option[A],
      status: Boolean = false
    ): List[Text.Info[A]] = {
      val former_range = revert(range).inflate_singularity
      val (chunk_name, command_iterator) =
        commands_loading.headOption match {
          case None => (Symbol.Text_Chunk.Default, node.command_iterator(former_range))
          case Some(command) => (Symbol.Text_Chunk.File(node_name.node), Iterator((command, 0)))
        }
      val markup_index = Command.Markup_Index(status, chunk_name)
      (for {
        (command, command_start) <- command_iterator
        chunk <- command.chunks.get(chunk_name).iterator
        states = state.command_states(version, command)
        res = result(states)
        markup_range <- (former_range - command_start).try_restrict(chunk.range).iterator
        markup = Command.State.merge_markup(states, markup_index, markup_range, elements)
        Text.Info(r0, a) <- markup.cumulate[A](markup_range, info, elements,
          {
            case (a, Text.Info(r0, b)) => res(a, Text.Info(convert(r0 + command_start), b))
          }).iterator
        r1 <- convert(r0 + command_start).try_restrict(range).iterator
      } yield Text.Info(r1, a)).toList
    }

    def select[A](
      range: Text.Range,
      elements: Markup.Elements,
      result: List[Command.State] => Text.Markup => Option[A],
      status: Boolean = false
    ): List[Text.Info[A]] = {
      def result1(states: List[Command.State]): (Option[A], Text.Markup) => Option[Option[A]] = {
        val res = result(states)
        (_: Option[A], x: Text.Markup) =>
          res(x) match {
            case None => None
            case some => Some(some)
          }
      }
      for (case Text.Info(r, Some(x)) <- cumulate(range, None, elements, result1, status))
        yield Text.Info(r, x)
    }
  }


  /* model */

  trait Session {
    def resources: Resources
  }

  trait Model {
    def session: Session
    def is_stable: Boolean
    def pending_edits: List[Text.Edit]

    def node_name: Node.Name
    def is_theory: Boolean = node_name.is_theory
    override def toString: String = node_name.toString

    def get_text(range: Text.Range): Option[String]

    def node_required: Boolean

    def get_blob: Option[Blobs.Item]

    def untyped_data: AnyRef
    def get_data[C](c: Class[C]): Option[C] = Library.as_subclass(c)(untyped_data)

    def node_edits(
      node_header: Node.Header,
      text_edits: List[Text.Edit],
      perspective: Node.Perspective_Text.T
    ): List[Edit_Text] = {
      val edits: List[Node.Edit[Text.Edit, Text.Perspective]] =
        get_blob match {
          case None =>
            List(
              Node.Deps(
                if (session.resources.session_base.loaded_theory(node_name)) {
                  node_header.append_errors(
                    List("Cannot update finished theory " + quote(node_name.theory)))
                }
                else node_header),
              Node.Edits(text_edits), perspective)
          case Some(blob) => List(Node.Blob(blob), Node.Edits(text_edits))
        }
      edits.flatMap(edit => if (edit.is_void) None else Some(node_name -> edit))
    }
  }


  /** global state -- document structure, execution process, editing history **/

  type Assign_Update =
    List[(Document_ID.Command, List[Document_ID.Exec])]  // update of exec state assignment

  object State {
    class Fail(state: State) extends Exception

    object Assignment {
      val init: Assignment = new Assignment()
    }

    final class Assignment private(
      val command_execs: Map[Document_ID.Command, List[Document_ID.Exec]] = Map.empty,
      val is_finished: Boolean = false
    ) {
      override def toString: String = "Assignment(" + command_execs.size + "," + is_finished + ")"

      def check_finished: Assignment = { require(is_finished, "assignment not finished"); this }
      def unfinished: Assignment = new Assignment(command_execs, false)

      def assign(update: Assign_Update): Assignment = {
        require(!is_finished, "assignment already finished")
        val command_execs1 =
          update.foldLeft(command_execs) {
            case (res, (command_id, exec_ids)) =>
              if (exec_ids.isEmpty) res - command_id
              else res + (command_id -> exec_ids)
          }
        new Assignment(command_execs1, true)
      }
    }

    val init: State =
      State().define_version(Version.init, Assignment.init).assign(Version.init.id, Nil, Nil)._2
  }

  final case class State private(
    /*reachable versions*/
    versions: Map[Document_ID.Version, Version] = Map.empty,
    /*inlined auxiliary files*/
    blobs: Set[SHA1.Digest] = Set.empty,
    /*loaded theories in batch builds*/
    theories: Map[Document_ID.Exec, Command.State] = Map.empty,
    /*static markup from define_command*/
    commands: Map[Document_ID.Command, Command.State] = Map.empty,
    /*dynamic markup from execution*/
    execs: Map[Document_ID.Exec, Command.State] = Map.empty,
    /*command-exec assignment for each version*/
    assignments: Map[Document_ID.Version, State.Assignment] = Map.empty,
    /*commands with markup produced by other commands (imm_succs)*/
    commands_redirection: Graph[Document_ID.Command, Unit] = Graph.long,
    /*explicit (linear) history*/
    history: History = History.init,
    /*intermediate state between remove_versions/removed_versions*/
    removing_versions: Boolean = false
  ) {
    override def toString: String =
      "State(versions = " + versions.size +
      ", blobs = " + blobs.size +
      ", commands = " + commands.size +
      ", execs = " + execs.size +
      ", assignments = " + assignments.size +
      ", commands_redirection = " + commands_redirection.size +
      ", history = " + history.undo_list.size +
      ", removing_versions = " + removing_versions + ")"

    private def fail[A]: A = throw new State.Fail(this)

    def define_version(version: Version, assignment: State.Assignment): State = {
      val id = version.id
      copy(versions = versions + (id -> version),
        assignments = assignments + (id -> assignment.unfinished))
    }

    def define_blob(digest: SHA1.Digest): State = copy(blobs = blobs + digest)
    def defined_blob(digest: SHA1.Digest): Boolean = blobs.contains(digest)

    def define_command(command: Command): State = {
      val id = command.id
      if (commands.isDefinedAt(id)) fail
      else copy(commands = commands + (id -> command.init_state))
    }

    def defined_command(id: Document_ID.Command): Boolean = commands.isDefinedAt(id)

    def the_version(id: Document_ID.Version): Version = versions.getOrElse(id, fail)
    def the_static_state(id: Document_ID.Command): Command.State = commands.getOrElse(id, fail)
    def the_dynamic_state(id: Document_ID.Exec): Command.State = execs.getOrElse(id, fail)
    def the_assignment(version: Version): State.Assignment = assignments.getOrElse(version.id, fail)

    def lookup_id(id: Document_ID.Generic): Option[Command.State] =
      theories.get(id) orElse commands.get(id) orElse execs.get(id)

    private def self_id(st: Command.State)(id: Document_ID.Generic): Boolean =
      id == st.command.id ||
      (execs.get(id) match { case Some(st1) => st1.command.id == st.command.id case None => false })

    private def other_id(
      node_name: Node.Name,
      id: Document_ID.Generic
    ) : Option[(Symbol.Text_Chunk.Id, Symbol.Text_Chunk)] = {
      for {
        st <- lookup_id(id)
        if st.command.node_name == node_name
      } yield (Symbol.Text_Chunk.Id(st.command.id), st.command.chunk)
    }

    private def redirection(st: Command.State): Graph[Document_ID.Command, Unit] =
      st.markups.redirection_iterator.foldLeft(commands_redirection) {
        case (graph, id) =>
          graph.default_node(id, ()).default_node(st.command.id, ()).add_edge(id, st.command.id)
      }

    def accumulate(
      id: Document_ID.Generic,
      message: XML.Elem,
      cache: XML.Cache
    ) : (Command.State, State) = {
      def update(st: Command.State): (Command.State, State) = {
        val st1 = st.accumulate(self_id(st), other_id, message, cache)
        (st1, copy(commands_redirection = redirection(st1)))
      }
      execs.get(id).map(update) match {
        case Some((st1, state1)) => (st1, state1.copy(execs = execs + (id -> st1)))
        case None =>
          commands.get(id).map(update) match {
            case Some((st1, state1)) => (st1, state1.copy(commands = commands + (id -> st1)))
            case None =>
              theories.get(id).map(update) match {
                case Some((st1, state1)) => (st1, state1.copy(theories = theories + (id -> st1)))
                case None => fail
              }
          }
      }
    }

    def add_export(
      id: Document_ID.Generic,
      entry: Command.Exports.Entry
    ): (Command.State, State) = {
      execs.get(id) match {
        case Some(st) =>
          st.add_export(entry) match {
            case Some(new_st) => (new_st, copy(execs = execs + (id -> new_st)))
            case None => fail
          }
        case None =>
          commands.get(id) match {
            case Some(st) =>
              st.add_export(entry) match {
                case Some(new_st) => (new_st, copy(commands = commands + (id -> new_st)))
                case None => fail
              }
            case None => fail
          }
      }
    }

    def node_exports(version: Version, node_name: Node.Name): Command.Exports =
      Command.Exports.merge(
        for {
          command <- version.nodes(node_name).commands.iterator
          st <- command_states(version, command).iterator
        } yield st.exports)

    def begin_theory(
      node_name: Node.Name,
      id: Document_ID.Exec,
      source: String,
      blobs_info: Command.Blobs_Info
    ): State = {
      if (theories.isDefinedAt(id)) fail
      else {
        val command =
          Command.unparsed(source, theory = true, id = id, node_name = node_name,
            blobs_info = blobs_info)
        copy(theories = theories + (id -> command.empty_state))
      }
    }

    def end_theory(id: Document_ID.Exec, document_blobs: Node.Name => Blobs): (Snapshot, State) =
      theories.get(id) match {
        case None => fail
        case Some(st) =>
          val command = st.command
          val node_name = command.node_name
          val doc_blobs = document_blobs(node_name)
          val command1 =
            Command.unparsed(command.source, theory = true, id = id, node_name = node_name,
              blobs_info = command.blobs_info, results = st.results, markups = st.markups)
          val state1 = copy(theories = theories - id)
          (state1.snippet(List(command1), doc_blobs), state1)
      }

    def assign(
      id: Document_ID.Version,
      edited: List[String],
      update: Assign_Update
    ) : ((List[Node.Name], List[Command]), State) = {
      val version = the_version(id)

      val edited_set = edited.toSet
      val edited_nodes =
        (for { (name, _) <- version.nodes.iterator if edited_set(name.node) } yield name).toList

      def upd(
        exec_id: Document_ID.Exec,
        st: Command.State
      ): Option[(Document_ID.Exec, Command.State)] = {
        if (execs.isDefinedAt(exec_id)) None else Some(exec_id -> st)
      }

      val (changed_commands, new_execs) =
        update.foldLeft((List.empty[Command], execs)) {
          case ((commands1, execs1), (command_id, exec)) =>
            val st = the_static_state(command_id)
            val command = st.command
            val commands2 = command :: commands1
            val execs2 =
              exec match {
                case Nil => execs1
                case eval_id :: print_ids =>
                  execs1 ++ upd(eval_id, st) ++
                    (for (id <- print_ids; up <- upd(id, command.empty_state)) yield up)
              }
            (commands2, execs2)
        }
      val new_assignment = the_assignment(version).assign(update)
      val new_state = copy(assignments = assignments + (id -> new_assignment), execs = new_execs)

      ((edited_nodes, changed_commands), new_state)
    }

    def is_assigned(version: Version): Boolean =
      assignments.get(version.id) match {
        case Some(assgn) => assgn.is_finished
        case None => false
      }

    def is_stable(change: Change): Boolean =
      change.is_finished && is_assigned(change.version.get_finished)

    def recent_finished: Change = history.undo_list.find(_.is_finished) getOrElse fail
    def recent_stable: Change = history.undo_list.find(is_stable) getOrElse fail
    def stable_tip_version: Option[Version] =
      if (is_stable(history.tip)) Some(history.tip.version.get_finished) else None

    def continue_history(
      previous: Future[Version],
      edits: List[Edit_Text],
      version: Future[Version]
    ): State = {
      val change = Change.make(previous, edits, version)
      copy(history = history + change)
    }

    def remove_versions(retain: Int = 0): (List[Version], State) = {
      history.prune(is_stable, retain) match {
        case Some((dropped, history1)) =>
          val old_versions = dropped.map(change => change.version.get_finished)
          val removing = old_versions.nonEmpty
          val state1 = copy(history = history1, removing_versions = removing)
          (old_versions, state1)
        case None => fail
      }
    }

    def removed_versions(removed: List[Document_ID.Version]): State = {
      val versions1 = Version.purge_suppressed(versions -- removed)

      val assignments1 = assignments -- removed
      var blobs1_names = Set.empty[Node.Name]
      var blobs1 = Set.empty[SHA1.Digest]
      var commands1 = Map.empty[Document_ID.Command, Command.State]
      var execs1 = Map.empty[Document_ID.Exec, Command.State]
      for {
        (version_id, version) <- versions1.iterator
        command_execs = assignments1(version_id).command_execs
        (_, node) <- version.nodes.iterator
        command <- node.commands.iterator
      } {
        for ((name, digest) <- command.blobs_defined) {
          blobs1_names += name
          blobs1 += digest
        }

        if (!commands1.isDefinedAt(command.id)) {
          commands.get(command.id).foreach(st => commands1 += (command.id -> st))
        }

        for {
          exec_id <- command_execs.getOrElse(command.id, Nil)
          if !execs1.isDefinedAt(exec_id)
          st <- execs.get(exec_id)
        } execs1 += (exec_id -> st)
      }

      copy(
        versions = versions1,
        blobs = blobs1,
        commands = commands1,
        execs = execs1,
        commands_redirection = commands_redirection.restrict(commands1.keySet),
        assignments = assignments1,
        history = history.purge(versions1),
        removing_versions = false)
    }

    def command_maybe_consolidated(version: Version, command: Command): Boolean = {
      require(is_assigned(version), "version not assigned (command_maybe_consolidated)")
      try {
        the_assignment(version).check_finished.command_execs.getOrElse(command.id, Nil) match {
          case eval_id :: print_ids =>
            the_dynamic_state(eval_id).maybe_consolidated &&
            !print_ids.exists(print_id => the_dynamic_state(print_id).consolidating)
          case Nil => false
        }
      }
      catch { case _: State.Fail => false }
    }

    private def command_states_self(
      version: Version,
      command: Command
    ) : List[(Document_ID.Generic, Command.State)] = {
      require(is_assigned(version), "version not assigned (command_states_self)")
      try {
        the_assignment(version).check_finished.command_execs.getOrElse(command.id, Nil)
          .map(id => id -> the_dynamic_state(id)) match {
            case Nil => fail
            case res => res
          }
      }
      catch {
        case _: State.Fail =>
          try { List(command.id -> the_static_state(command.id)) }
          catch { case _: State.Fail => List(command.id -> command.init_state) }
      }
    }

    def command_states(version: Version, command: Command): List[Command.State] = {
      val self = command_states_self(version, command)
      val others =
        if (commands_redirection.defined(command.id)) {
          (for {
            command_id <- commands_redirection.imm_succs(command.id).iterator
            (id, st) <- command_states_self(version, the_static_state(command_id).command)
            if !self.exists(_._1 == id)
          } yield (id, st)).toMap.valuesIterator.toList
        }
        else Nil
      self.map(_._2) ::: others.flatMap(_.redirect(command))
    }

    def command_results(version: Version, command: Command): Command.Results =
      Command.State.merge_results(command_states(version, command))

    def command_markup(version: Version, command: Command, index: Command.Markup_Index,
        range: Text.Range, elements: Markup.Elements): Markup_Tree =
      Command.State.merge_markup(command_states(version, command), index, range, elements)

    def xml_markup(
      version: Version,
      node_name: Node.Name,
      range: Text.Range = Text.Range.full,
      elements: Markup.Elements = Markup.Elements.full
    ): XML.Body = {
      val node = version.nodes(node_name)
      if (node_name.is_theory) {
        val markup_index = Command.Markup_Index.markup
        (for {
          command <- node.commands.iterator
          command_range <- command.range.try_restrict(range).iterator
          markup = command_markup(version, command, markup_index, command_range, elements)
          tree <- markup.to_XML(command_range, command.source, elements).iterator
        } yield tree).toList
      }
      else if (node.source_wellformed) {
        Text.Range.length(node.source).try_restrict(range) match {
          case Some(node_range) =>
            val markup =
              version.nodes.commands_loading(node_name).headOption match {
                case None => Markup_Tree.empty
                case Some(command) =>
                  val chunk_name = Symbol.Text_Chunk.File(node_name.node)
                  val markup_index = Command.Markup_Index(false, chunk_name)
                  command_markup(version, command, markup_index, node_range, elements)
              }
            markup.to_XML(node_range, node.source, elements)
          case None => Nil
        }
      }
      else Nil
    }

    def node_initialized(version: Version, name: Node.Name): Boolean =
      name.is_theory &&
      (version.nodes(name).commands.iterator.find(_.potentially_initialized) match {
        case None => false
        case Some(command) => command_states(version, command).headOption.exists(_.initialized)
      })

    def node_maybe_consolidated(version: Version, name: Node.Name): Boolean =
      name.is_theory &&
      version.nodes(name).commands.reverse.iterator.forall(command_maybe_consolidated(version, _))

    def node_consolidated(version: Version, name: Node.Name): Boolean =
      !name.is_theory || {
        val it = version.nodes(name).commands.reverse.iterator
        it.hasNext && command_states(version, it.next()).exists(_.consolidated)
      }

    def snapshot(
      node_name: Node.Name = Node.Name.empty,
      pending_edits: Pending_Edits = Pending_Edits.empty,
      snippet_commands: List[Command] = Nil
    ): Snapshot = {
      val stable = recent_stable
      val version = stable.version.get_finished

      val pending_edits1 =
        (for {
          change <- history.undo_list.takeWhile(_ != stable)
          case (name, Node.Edits(es)) <- change.rev_edits
        } yield (name -> es)).foldLeft(pending_edits)(_ + _)

      new Snapshot(this, version, node_name, pending_edits1, snippet_commands)
    }

    def snippet(commands: List[Command], doc_blobs: Blobs): Snapshot =
      snapshot().snippet(commands, doc_blobs)
  }
}
