/*  Title:      Pure/PIDE/resources.scala
    Author:     Makarius

Resources for theories and auxiliary files.
*/

package isabelle


import scala.util.parsing.input.Reader

import java.io.{File => JFile}


class Resources(
  val sessions_structure: Sessions.Structure,
  val session_base: Sessions.Base,
  val log: Logger = No_Logger,
  command_timings: List[Properties.T] = Nil)
{
  resources =>


  /* init session */

  def init_session_yxml: String =
  {
    import XML.Encode._

    YXML.string_of_body(
      pair(list(pair(string, properties)),
      pair(list(pair(string, string)),
      pair(list(pair(string, string)),
      pair(list(pair(string, list(string))),
      pair(list(properties),
      pair(list(pair(string, properties)),
      pair(list(pair(string, string)), list(string))))))))(
       (sessions_structure.session_positions,
       (sessions_structure.dest_session_directories,
       (sessions_structure.session_chapters,
       (sessions_structure.bibtex_entries,
       (command_timings,
       (Scala.functions.map(fun => (fun.name, fun.position)),
       (session_base.global_theories.toList,
        session_base.loaded_theories.keys)))))))))
  }


  /* file formats */

  def make_theory_name(name: Document.Node.Name): Option[Document.Node.Name] =
    File_Format.registry.get(name).flatMap(_.make_theory_name(resources, name))

  def make_theory_content(thy_name: Document.Node.Name): Option[String] =
    File_Format.registry.get_theory(thy_name).flatMap(_.make_theory_content(resources, thy_name))

  def make_preview(snapshot: Document.Snapshot): Option[Presentation.Preview] =
    File_Format.registry.get(snapshot.node_name).flatMap(_.make_preview(snapshot))

  def is_hidden(name: Document.Node.Name): Boolean =
    !name.is_theory || name.theory == Sessions.root_name || File_Format.registry.is_theory(name)

  def thy_path(path: Path): Path = path.ext("thy")


  /* file-system operations */

  def append(dir: String, source_path: Path): String =
    (Path.explode(dir) + source_path).expand.implode

  def append(node_name: Document.Node.Name, source_path: Path): String =
    append(node_name.master_dir, source_path)

  def make_theory_node(dir: String, file: Path, theory: String): Document.Node.Name =
  {
    val node = append(dir, file)
    val master_dir = append(dir, file.dir)
    Document.Node.Name(node, master_dir, theory)
  }

  def loaded_theory_node(theory: String): Document.Node.Name =
    Document.Node.Name(theory, "", theory)


  /* source files of Isabelle/ML bootstrap */

  def source_file(raw_name: String): Option[String] =
  {
    if (Path.is_wellformed(raw_name)) {
      if (Path.is_valid(raw_name)) {
        def check(p: Path): Option[Path] = if (p.is_file) Some(p) else None

        val path = Path.explode(raw_name)
        val path1 =
          if (path.is_absolute || path.is_current) check(path)
          else {
            check(Path.explode("~~/src/Pure") + path) orElse
              (if (Isabelle_System.getenv("ML_SOURCES") == "") None
               else check(Path.explode("$ML_SOURCES") + path))
          }
        Some(File.platform_path(path1 getOrElse path))
      }
      else None
    }
    else Some(raw_name)
  }


  /* theory files */

  def loaded_files(syntax: Outer_Syntax, name: Document.Node.Name): () => List[Path] =
  {
    val (is_utf8, raw_text) =
      with_thy_reader(name, reader => (Scan.reader_is_utf8(reader), reader.source.toString))
    () => {
      if (syntax.has_load_commands(raw_text)) {
        val text = Symbol.decode(Scan.reader_decode_utf8(is_utf8, raw_text))
        val spans = syntax.parse_spans(text)
        val dir = Path.explode(name.master_dir)
        (for {
          span <- spans.iterator
          file <- span.loaded_files(syntax).files
        } yield (dir + Path.explode(file)).expand).toList
      }
      else Nil
    }
  }

  def pure_files(syntax: Outer_Syntax): List[Path] =
  {
    val pure_dir = Path.explode("~~/src/Pure")
    val roots =
      for { (name, _) <- Thy_Header.ml_roots }
      yield (pure_dir + Path.explode(name)).expand
    val files =
      for {
        (path, (_, theory)) <- roots zip Thy_Header.ml_roots
        file <- loaded_files(syntax, Document.Node.Name(path.implode, path.dir.implode, theory))()
      } yield file
    roots ::: files
  }

  def theory_name(qualifier: String, theory: String): String =
    if (Long_Name.is_qualified(theory) || session_base.global_theories.isDefinedAt(theory))
      theory
    else Long_Name.qualify(qualifier, theory)

  def find_theory_node(theory: String): Option[Document.Node.Name] =
  {
    val thy_file = thy_path(Path.basic(Long_Name.base_name(theory)))
    val session = session_base.theory_qualifier(theory)
    val dirs =
      sessions_structure.get(session) match {
        case Some(info) => info.dirs
        case None => Nil
      }
    dirs.collectFirst({
      case dir if (dir + thy_file).is_file => make_theory_node("", dir + thy_file, theory) })
  }

  def import_name(qualifier: String, dir: String, s: String): Document.Node.Name =
  {
    val theory = theory_name(qualifier, Thy_Header.import_name(s))
    def theory_node = make_theory_node(dir, thy_path(Path.explode(s)), theory)

    if (!Thy_Header.is_base_name(s)) theory_node
    else if (session_base.loaded_theory(theory)) loaded_theory_node(theory)
    else {
      find_theory_node(theory) match {
        case Some(node_name) => node_name
        case None => if (Long_Name.is_qualified(s)) loaded_theory_node(theory) else theory_node
      }
    }
  }

  def import_name(name: Document.Node.Name, s: String): Document.Node.Name =
    import_name(session_base.theory_qualifier(name), name.master_dir, s)

  def import_name(info: Sessions.Info, s: String): Document.Node.Name =
    import_name(info.name, info.dir.implode, s)

  def find_theory(file: JFile): Option[Document.Node.Name] =
  {
    for {
      qualifier <- session_base.session_directories.get(File.canonical(file).getParentFile)
      theory_base <- proper_string(Thy_Header.theory_name(file.getName))
      theory = theory_name(qualifier, theory_base)
      theory_node <- find_theory_node(theory)
      if File.eq(theory_node.path.file, file)
    } yield theory_node
  }

  def complete_import_name(context_name: Document.Node.Name, s: String): List[String] =
  {
    val context_session = session_base.theory_qualifier(context_name)
    val context_dir =
      try { Some(context_name.master_dir_path) }
      catch { case ERROR(_) => None }
    (for {
      (session, (info, _))  <- sessions_structure.imports_graph.iterator
      dir <- (if (session == context_session) context_dir.toList else info.dirs).iterator
      theory <- Thy_Header.try_read_dir(dir).iterator
      if Completion.completed(s)(theory)
    } yield {
      if (session == context_session || session_base.global_theories.isDefinedAt(theory)) theory
      else Long_Name.qualify(session, theory)
    }).toList.sorted
  }

  def with_thy_reader[A](name: Document.Node.Name, f: Reader[Char] => A): A =
  {
    val path = name.path
    if (path.is_file) using(Scan.byte_reader(path.file))(f)
    else if (name.node == name.theory)
      error("Cannot load theory " + quote(name.theory))
    else error ("Cannot load theory file " + path)
  }

  def check_thy_reader(node_name: Document.Node.Name, reader: Reader[Char],
    start: Token.Pos = Token.Pos.command, strict: Boolean = true): Document.Node.Header =
  {
    if (node_name.is_theory && reader.source.length > 0) {
      try {
        val header = Thy_Header.read(reader, start, strict).check_keywords

        val base_name = node_name.theory_base_name
        if (Long_Name.is_qualified(header.name)) {
          error("Bad theory name " + quote(header.name) + " with qualification" +
            Position.here(header.pos))
        }
        if (base_name != header.name) {
          error("Bad theory name " + quote(header.name) +
            " for file " + thy_path(Path.basic(base_name)) + Position.here(header.pos) +
            Completion.report_theories(header.pos, List(base_name)))
        }

        val imports_pos =
          header.imports_pos.map({ case (s, pos) =>
            val name = import_name(node_name, s)
            if (Sessions.exclude_theory(name.theory_base_name))
              error("Bad theory name " + quote(name.theory_base_name) + Position.here(pos))
            (name, pos)
          })
        Document.Node.Header(imports_pos, header.keywords, header.abbrevs)
      }
      catch { case exn: Throwable => Document.Node.bad_header(Exn.message(exn)) }
    }
    else Document.Node.no_header
  }

  def check_thy(name: Document.Node.Name, start: Token.Pos = Token.Pos.command,
      strict: Boolean = true): Document.Node.Header =
    with_thy_reader(name, check_thy_reader(name, _, start, strict))


  /* special header */

  def special_header(name: Document.Node.Name): Option[Document.Node.Header] =
  {
    val imports =
      if (name.theory == Sessions.root_name) List(import_name(name, Sessions.theory_name))
      else if (Thy_Header.is_ml_root(name.theory)) List(import_name(name, Thy_Header.ML_BOOTSTRAP))
      else if (Thy_Header.is_bootstrap(name.theory)) List(import_name(name, Thy_Header.PURE))
      else Nil
    if (imports.isEmpty) None
    else Some(Document.Node.Header(imports.map((_, Position.none))))
  }


  /* blobs */

  def undefined_blobs(nodes: Document.Nodes): List[Document.Node.Name] =
    (for {
      (node_name, node) <- nodes.iterator
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

  def commit(change: Session.Change) { }


  /* theory and file dependencies */

  def dependencies(
      thys: List[(Document.Node.Name, Position.T)],
      progress: Progress = new Progress): Dependencies[Unit] =
    Dependencies.empty[Unit].require_thys((), thys, progress = progress)

  def session_dependencies(info: Sessions.Info, progress: Progress = new Progress)
    : Dependencies[Options] =
  {
    (Dependencies.empty[Options] /: info.theories)({ case (dependencies, (options, thys)) =>
      dependencies.require_thys(options,
        for { (thy, pos) <- thys } yield (import_name(info, thy), pos),
        progress = progress)
    })
  }

  object Dependencies
  {
    def empty[A]: Dependencies[A] = new Dependencies[A](Nil, Map.empty)

    private def show_path(names: List[Document.Node.Name]): String =
      names.map(name => quote(name.theory)).mkString(" via ")

    private def cycle_msg(names: List[Document.Node.Name]): String =
      "Cyclic dependency of " + show_path(names)

    private def required_by(initiators: List[Document.Node.Name]): String =
      if (initiators.isEmpty) ""
      else "\n(required by " + show_path(initiators.reverse) + ")"
  }

  final class Dependencies[A] private(
    rev_entries: List[Document.Node.Entry],
    seen: Map[Document.Node.Name, A])
  {
    private def cons(entry: Document.Node.Entry): Dependencies[A] =
      new Dependencies[A](entry :: rev_entries, seen)

    def require_thy(adjunct: A,
      thy: (Document.Node.Name, Position.T),
      initiators: List[Document.Node.Name] = Nil,
      progress: Progress = new Progress): Dependencies[A] =
    {
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
              try { check_thy(name, Token.Pos.file(name.node)).cat_errors(message) }
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
        initiators: List[Document.Node.Name] = Nil): Dependencies[A] =
      (this /: thys)(_.require_thy(adjunct, _, progress = progress, initiators = initiators))

    def entries: List[Document.Node.Entry] = rev_entries.reverse

    def theories: List[Document.Node.Name] = entries.map(_.name)
    def theories_adjunct: List[(Document.Node.Name, A)] = theories.map(name => (name, seen(name)))

    def errors: List[String] = entries.flatMap(_.header.errors)

    def check_errors: Dependencies[A] =
      errors match {
        case Nil => this
        case errs => error(cat_lines(errs))
      }

    lazy val theory_graph: Document.Node.Name.Graph[Unit] =
    {
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
      (session_base.loaded_theories /: entries)({ case (graph, entry) =>
        val name = entry.name.theory
        val imports = entry.header.imports.map(_.theory)

        val graph1 = (graph /: (name :: imports))(_.default_node(_, Outer_Syntax.empty))
        val graph2 = (graph1 /: imports)(_.add_edge(_, name))

        val syntax0 = if (name == Thy_Header.PURE) List(Thy_Header.bootstrap_syntax) else Nil
        val syntax1 = (name :: graph2.imm_preds(name).toList).map(graph2.get_node)
        val syntax = Outer_Syntax.merge(syntax0 ::: syntax1) + entry.header

        graph2.map_node(name, _ => syntax)
      })

    def loaded_files(pure: Boolean): List[(String, List[Path])] =
    {
      val loaded_files =
        theories.map(_.theory) zip
          Par_List.map((e: () => List[Path]) => e(),
            theories.map(name =>
              resources.loaded_files(loaded_theories.get_node(name.theory), name)))

      if (pure) {
        val pure_files = resources.pure_files(overall_syntax)
        loaded_files.map({ case (name, files) =>
          (name, if (name == Thy_Header.PURE) pure_files ::: files else files) })
      }
      else loaded_files
    }

    def imported_files: List[Path] =
    {
      val base_theories =
        loaded_theories.all_preds(theories.map(_.theory)).
          filter(session_base.loaded_theories.defined)

      base_theories.map(theory => session_base.known_theories(theory).name.path) :::
      base_theories.flatMap(session_base.known_loaded_files(_))
    }

    lazy val overall_syntax: Outer_Syntax =
      Outer_Syntax.merge(loaded_theories.maximals.map(loaded_theories.get_node))

    override def toString: String = entries.toString
  }
}
