/*  Title:      Pure/Build/resources.scala
    Author:     Makarius

Resources for theories and auxiliary files.
*/

package isabelle


import scala.util.parsing.input.Reader

import java.io.{File => JFile}


object Resources {
  def bootstrap: Resources = new Resources(Sessions.Background(base = Sessions.Base.bootstrap))

  def hidden_node(name: Document.Node.Name): Boolean =
    !name.is_theory || name.theory == Sessions.root_name || File_Format.registry.is_theory(name)

  def html_document(snapshot: Document.Snapshot): Option[Browser_Info.HTML_Document] =
    File_Format.registry.get(snapshot.node_name).flatMap(_.html_document(snapshot))
}

class Resources(
  val session_background: Sessions.Background,
  val log: Logger = new Logger,
  command_timings: List[Properties.T] = Nil
) {
  resources =>

  def sessions_structure: Sessions.Structure = session_background.sessions_structure
  def session_base: Sessions.Base = session_background.base

  override def toString: String = "Resources(" + session_base.print_body + ")"


  /* init session */

  def init_session_xml: XML.Body = {
    import XML.Encode._

    pair(list(pair(string, properties)),
    pair(list(pair(string, string)),
    pair(list(properties),
    pair(list(pair(string, properties)),
    pair(list(Scala.encode_fun),
    pair(list(pair(string, string)), list(string)))))))(
     (sessions_structure.session_positions,
     (sessions_structure.dest_session_directories,
     (command_timings,
     (Command_Span.load_commands.map(cmd => (cmd.name, cmd.position)),
     (Scala.functions,
     (sessions_structure.global_theories.toList,
      session_base.loaded_theories.keys)))))))
  }


  /* file formats */

  def make_theory_name(name: Document.Node.Name): Option[Document.Node.Name] =
    File_Format.registry.get(name).flatMap(_.make_theory_name(resources, name))

  def make_theory_content(thy_name: Document.Node.Name): Option[String] =
    File_Format.registry.get_theory(thy_name).flatMap(_.make_theory_content(resources, thy_name))


  /* file-system operations */

  def migrate_name(name: Document.Node.Name): Document.Node.Name = name

  def append_path(prefix: String, source_path: Path): String =
    File.standard_path(Path.explode(prefix) + source_path)

  def read_dir(dir: String): List[String] = File.read_dir(Path.explode(dir))

  def list_thys(dir: String): List[String] = {
    val entries = try { read_dir(dir) } catch { case ERROR(_) => Nil }
    entries.flatMap(Thy_Header.get_thy_name)
  }


  /* theory files */

  def load_commands(
    syntax: Outer_Syntax,
    name: Document.Node.Name
  ) : () => List[Command_Span.Span] = {
    val (is_utf8, raw_text) =
      with_thy_reader(name, reader => (Scan.reader_is_utf8(reader), reader.source.toString))
    () =>
      {
        if (syntax.has_load_commands(raw_text)) {
          val text = Symbol.decode(Scan.reader_decode_utf8(is_utf8, raw_text))
          syntax.parse_spans(text).filter(_.is_load_command(syntax))
        }
        else Nil
      }
  }

  def loaded_files(
    syntax: Outer_Syntax,
    name: Document.Node.Name,
    spans: List[Command_Span.Span]
  ) : List[Document.Node.Name] = {
    for (span <- spans; file <- span.loaded_files(syntax).files)
      yield Document.Node.Name(append_path(name.master_dir, Path.explode(file)))
  }

  def pure_files(syntax: Outer_Syntax): List[Document.Node.Name] =
    (for {
      (file, theory) <- Thy_Header.ml_roots.iterator
      node = append_path("~~/src/Pure", Path.explode(file))
      node_name = Document.Node.Name(node, theory = theory)
      name <- loaded_files(syntax, node_name, load_commands(syntax, node_name)()).iterator
    } yield name).toList

  def global_theory(theory: String): Boolean =
    sessions_structure.global_theories.isDefinedAt(theory)

  def literal_theory(theory: String): Boolean =
    Long_Name.is_qualified(theory) || global_theory(theory)

  def theory_name(qualifier: String, theory: String): String =
    if (literal_theory(theory)) theory
    else Long_Name.qualify(qualifier, theory)

  def find_theory_node(theory: String): Option[Document.Node.Name] = {
    val thy_file = Path.basic(Long_Name.base_name(theory)).thy
    val session = sessions_structure.theory_qualifier(theory)
    val dirs =
      sessions_structure.get(session) match {
        case Some(info) => info.dirs
        case None => Nil
      }
    dirs.collectFirst { case dir if (dir + thy_file).is_file =>
      Document.Node.Name(append_path("", dir + thy_file), theory = theory) }
  }

  def import_name(qualifier: String, prefix: String, s: String): Document.Node.Name = {
    val theory = theory_name(qualifier, Thy_Header.import_name(s))
    val literal_import =
      literal_theory(theory) && qualifier != sessions_structure.theory_qualifier(theory)
    if (literal_import && !Url.is_base_name(s)) {
      error("Bad import of theory from other session via file-path: " + quote(s))
    }
    if (session_base.loaded_theory(theory)) Document.Node.Name.loaded_theory(theory)
    else {
      find_theory_node(theory) match {
        case Some(node_name) => node_name
        case None =>
          if (Url.is_base_name(s) && literal_theory(s)) Document.Node.Name.loaded_theory(theory)
          else Document.Node.Name(append_path(prefix, Path.explode(s).thy), theory = theory)
      }
    }
  }

  def import_name(name: Document.Node.Name, s: String): Document.Node.Name =
    import_name(sessions_structure.theory_qualifier(name), name.master_dir, s)

  def import_name(info: Sessions.Info, s: String): Document.Node.Name =
    import_name(info.name, info.dir.implode, s)

  def find_theory(file: JFile): Option[Document.Node.Name] = {
    for {
      qualifier <- sessions_structure.session_directories.get(File.canonical(file).getParentFile)
      theory_base <- proper_string(Thy_Header.theory_name(file.getName))
      theory = theory_name(qualifier, theory_base)
      theory_node <- find_theory_node(theory)
      if File.eq(theory_node.path.file, file)
    } yield theory_node
  }

  def complete_import_name(context_name: Document.Node.Name, s: String): List[String] = {
    val context_session = sessions_structure.theory_qualifier(context_name)
    def context_dir(): List[String] = list_thys(context_name.master_dir)
    def session_dir(info: Sessions.Info): List[String] = info.dirs.flatMap(Thy_Header.list_thys)
    (for {
      (session, (info, _)) <- sessions_structure.imports_graph.iterator
      theory <- (if (session == context_session) context_dir() else session_dir(info)).iterator
      if Completion.completed(s)(theory)
    } yield {
      if (session == context_session || global_theory(theory)) theory
      else Long_Name.qualify(session, theory)
    }).toList.sorted
  }

  def with_thy_reader[A](name: Document.Node.Name, f: Reader[Char] => A): A = {
    val path = name.path
    if (path.is_file) using(Scan.byte_reader(path.file))(f)
    else if (name.node == name.theory)
      error("Cannot load theory " + quote(name.theory))
    else error ("Cannot load theory file " + path)
  }

  def check_thy(
    node_name: Document.Node.Name,
    reader: Reader[Char],
    command: Boolean = true,
    strict: Boolean = true
  ): Document.Node.Header = {
    if (node_name.is_theory && reader.source.length > 0) {
      try {
        val header = Thy_Header.read(node_name, reader, command = command, strict = strict)
        val imports =
          header.imports.map({ case (s, pos) =>
            val name = import_name(node_name, s)
            if (Sessions.illegal_theory(name.theory_base_name)) {
              error("Illegal theory name " + quote(name.theory_base_name) + Position.here(pos))
            }
            else (name, pos)
          })
        Document.Node.Header(imports, header.keywords, header.abbrevs)
      }
      catch { case exn: Throwable => Document.Node.bad_header(Exn.message(exn)) }
    }
    else Document.Node.no_header
  }


  /* special header */

  def special_header(name: Document.Node.Name): Option[Document.Node.Header] = {
    val imports =
      if (name.theory == Sessions.root_name) List(import_name(name, Sessions.theory_import))
      else if (Thy_Header.is_ml_root(name.theory)) List(import_name(name, Thy_Header.ML_BOOTSTRAP))
      else if (Thy_Header.is_bootstrap(name.theory)) List(import_name(name, Thy_Header.PURE))
      else Nil
    if (imports.isEmpty) None
    else Some(Document.Node.Header(imports.map((_, Position.none))))
  }


  /* blobs */

  def undefined_blobs(version: Document.Version): List[Document.Node.Name] =
    (for {
      (node_name, node) <- version.nodes.iterator
      if !session_base.loaded_theory(node_name)
      cmd <- node.load_commands.iterator
      name <- cmd.blobs_undefined.iterator
    } yield name).toList


  /* document changes */

  def parse_change(
      reparse_limit: Int,
      previous: Document.Version,
      doc_blobs: Document.Blobs,
      edits: List[Document.Edit_Text],
      consolidate: List[Document.Node.Name]): Session.Change =
    Thy_Syntax.parse_change(resources, reparse_limit, previous, doc_blobs, edits, consolidate)


  /* theory and file dependencies */

  def dependencies(
      thys: List[(Document.Node.Name, Position.T)],
      progress: Progress = new Progress): Dependencies[Unit] =
    Dependencies.empty[Unit].require_thys((), thys, progress = progress)

  def session_dependencies(
    info: Sessions.Info,
    progress: Progress = new Progress
  ) : Dependencies[Options] = {
    info.theories.foldLeft(Dependencies.empty[Options]) {
      case (dependencies, (options, thys)) =>
        dependencies.require_thys(options,
          for { (thy, pos) <- thys } yield (import_name(info, thy), pos),
          progress = progress)
    }
  }

  object Dependencies {
    def empty[A]: Dependencies[A] = new Dependencies[A](Nil, Map.empty)

    private def show_path(names: List[Document.Node.Name]): String =
      names.map(name => quote(name.theory)).mkString(" via ")

    private def cycle_msg(names: List[Document.Node.Name]): String =
      "Cyclic dependency of " + show_path(names)

    private def required_by(initiators: List[Document.Node.Name]): String =
      if_proper(initiators, "\n(required by " + show_path(initiators.reverse) + ")")
  }

  final class Dependencies[A] private(
    rev_entries: List[Document.Node.Entry],
    seen: Map[Document.Node.Name, A]
  ) {
    private def cons(entry: Document.Node.Entry): Dependencies[A] =
      new Dependencies[A](entry :: rev_entries, seen)

    def require_thy(adjunct: A,
      thy: (Document.Node.Name, Position.T),
      initiators: List[Document.Node.Name] = Nil,
      progress: Progress = new Progress
    ): Dependencies[A] = {
      val (name, pos) = thy

      def message: String =
        "The error(s) above occurred for theory " + quote(name.theory) +
          Dependencies.required_by(initiators) + Position.here(pos)

      if (seen.isDefinedAt(name)) this
      else {
        val dependencies1 = new Dependencies[A](rev_entries, seen + (name -> adjunct))
        if (session_base.loaded_theory(name)) dependencies1
        else {
          try {
            if (initiators.contains(name)) error(Dependencies.cycle_msg(initiators))

            progress.expose_interrupt()
            val header =
              try {
                with_thy_reader(name, check_thy(name, _, command = false)).cat_errors(message)
              }
              catch { case ERROR(msg) => cat_error(msg, message) }
            val entry = Document.Node.Entry(name, header)
            dependencies1.require_thys(adjunct, header.imports_pos,
              initiators = name :: initiators, progress = progress).cons(entry)
          }
          catch {
            case e: Throwable =>
              dependencies1.cons(Document.Node.Entry(name, Document.Node.bad_header(Exn.message(e))))
          }
        }
      }
    }

    def require_thys(adjunct: A,
        thys: List[(Document.Node.Name, Position.T)],
        progress: Progress = new Progress,
        initiators: List[Document.Node.Name] = Nil
    ): Dependencies[A] = {
      thys.foldLeft(this)(_.require_thy(adjunct, _, progress = progress, initiators = initiators))
    }

    def entries: List[Document.Node.Entry] = rev_entries.reverse

    def theories: List[Document.Node.Name] = entries.map(_.name)
    def theories_adjunct: List[(Document.Node.Name, A)] = theories.map(name => (name, seen(name)))

    def errors: List[String] = entries.flatMap(_.header.errors)

    def check_errors: Dependencies[A] =
      errors match {
        case Nil => this
        case errs => error(cat_lines(errs))
      }

    lazy val theory_graph: Document.Node.Name.Graph[Unit] = {
      val regular = theories.toSet
      val irregular =
        (for {
          entry <- entries.iterator
          imp <- entry.header.imports
          if !regular(imp)
        } yield imp).toSet

      Document.Node.Name.make_graph(
        irregular.toList.map(name => ((name, ()), Nil)) :::
        entries.map(entry => ((entry.name, ()), entry.header.imports)))
    }

    lazy val loaded_theories: Graph[String, Outer_Syntax] =
      entries.foldLeft(session_base.loaded_theories) {
        case (graph, entry) =>
          val name = entry.name.theory
          val imports = entry.header.imports.map(_.theory)

          val graph1 = (name :: imports).foldLeft(graph)(_.default_node(_, Outer_Syntax.empty))
          val graph2 = imports.foldLeft(graph1)(_.add_edge(_, name))

          val syntax0 = if (name == Thy_Header.PURE) List(Thy_Header.bootstrap_syntax) else Nil
          val syntax1 = (name :: graph2.imm_preds(name).toList).map(graph2.get_node)
          val syntax = Outer_Syntax.merge(syntax0 ::: syntax1) + entry.header

          graph2.map_node(name, _ => syntax)
      }

    def get_syntax(name: Document.Node.Name): Outer_Syntax =
      loaded_theories.get_node(name.theory)

    lazy val load_commands: List[(Document.Node.Name, List[Command_Span.Span])] =
      theories.zip(
        Par_List.map((e: () => List[Command_Span.Span]) => e(),
          theories.map(name => resources.load_commands(get_syntax(name), name))))
      .filter(p => p._2.nonEmpty)

    def loaded_files(
      name: Document.Node.Name,
      spans: List[Command_Span.Span]
    ) : (String, List[Document.Node.Name]) = {
      val theory = name.theory
      val syntax = get_syntax(name)
      val files1 = resources.loaded_files(syntax, name, spans)
      val files2 = if (theory == Thy_Header.PURE) pure_files(syntax) else Nil
      (theory, files1 ::: files2)
    }

    def loaded_files: List[Document.Node.Name] =
      for {
        (name, spans) <- load_commands
        file <- loaded_files(name, spans)._2
      } yield file

    def imported_files: List[Path] = {
      val base_theories =
        loaded_theories.all_preds(theories.map(_.theory)).
          filter(session_base.loaded_theories.defined)

      base_theories.map(theory => session_base.known_theories(theory).name.path) :::
      base_theories.flatMap(session_base.known_loaded_files.withDefaultValue(Nil))
    }

    lazy val overall_syntax: Outer_Syntax =
      Outer_Syntax.merge(loaded_theories.maximals.map(loaded_theories.get_node))

    override def toString: String = entries.toString
  }


  /* resolve implicit theory dependencies */

  def resolve_dependencies[A](
    models: Iterable[Document.Model],
    theories: List[Document.Node.Name]
  ): List[Document.Node.Name] = {
    val model_theories =
      (for (model <- models.iterator if model.is_theory)
        yield (model.node_name, Position.none)).toList

    val thy_files1 =
      dependencies(model_theories ::: theories.map((_, Position.none))).theories

    val thy_files2 =
      (for {
        model <- models.iterator if !model.is_theory
        thy_name <- make_theory_name(model.node_name)
      } yield thy_name).toList

    thy_files1 ::: thy_files2
  }
}
