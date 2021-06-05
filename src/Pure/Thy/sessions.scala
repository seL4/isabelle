/*  Title:      Pure/Thy/sessions.scala
    Author:     Makarius

Cumulative session information.
*/

package isabelle

import java.io.{File => JFile}
import java.nio.ByteBuffer
import java.nio.channels.FileChannel
import java.nio.file.StandardOpenOption

import scala.collection.immutable.{SortedSet, SortedMap}
import scala.collection.mutable


object Sessions
{
  /* session and theory names */

  val ROOTS: Path = Path.explode("ROOTS")
  val ROOT: Path = Path.explode("ROOT")

  val roots_name: String = "ROOTS"
  val root_name: String = "ROOT"
  val theory_name: String = "Pure.Sessions"

  val UNSORTED = "Unsorted"
  val DRAFT = "Draft"

  def is_pure(name: String): Boolean = name == Thy_Header.PURE


  def exclude_session(name: String): Boolean = name == "" || name == DRAFT

  def exclude_theory(name: String): Boolean =
    name == root_name || name == "README" || name == "index" || name == "bib"


  /* ROOTS file format */

  class File_Format extends isabelle.File_Format
  {
    val format_name: String = roots_name
    val file_ext = ""

    override def detect(name: String): Boolean =
      Thy_Header.split_file_name(name) match {
        case Some((_, file_name)) => file_name == roots_name
        case None => false
      }

    override def theory_suffix: String = "ROOTS_file"
    override def theory_content(name: String): String =
      """theory "ROOTS" imports Pure begin ROOTS_file """ +
        Outer_Syntax.quote_string(name) + """ end"""
  }


  /* base info and source dependencies */

  sealed case class Base(
    pos: Position.T = Position.none,
    session_directories: Map[JFile, String] = Map.empty,
    global_theories: Map[String, String] = Map.empty,
    session_theories: List[Document.Node.Name] = Nil,
    document_theories: List[Document.Node.Name] = Nil,
    loaded_theories: Graph[String, Outer_Syntax] = Graph.string,
    used_theories: List[(Document.Node.Name, Options)] = Nil,
    load_commands: Map[Document.Node.Name, List[Command_Span.Span]] = Map.empty,
    known_theories: Map[String, Document.Node.Entry] = Map.empty,
    known_loaded_files: Map[String, List[Path]] = Map.empty,
    overall_syntax: Outer_Syntax = Outer_Syntax.empty,
    imported_sources: List[(Path, SHA1.Digest)] = Nil,
    sources: List[(Path, SHA1.Digest)] = Nil,
    session_graph_display: Graph_Display.Graph = Graph_Display.empty_graph,
    errors: List[String] = Nil)
  {
    override def toString: String =
      "Sessions.Base(loaded_theories = " + loaded_theories.size +
        ", used_theories = " + used_theories.length + ")"

    def theory_qualifier(name: String): String =
      global_theories.getOrElse(name, Long_Name.qualifier(name))
    def theory_qualifier(name: Document.Node.Name): String = theory_qualifier(name.theory)

    def loaded_theory(name: String): Boolean = loaded_theories.defined(name)
    def loaded_theory(name: Document.Node.Name): Boolean = loaded_theory(name.theory)

    def loaded_theory_syntax(name: String): Option[Outer_Syntax] =
      if (loaded_theory(name)) Some(loaded_theories.get_node(name)) else None
    def loaded_theory_syntax(name: Document.Node.Name): Option[Outer_Syntax] =
      loaded_theory_syntax(name.theory)

    def theory_syntax(name: Document.Node.Name): Outer_Syntax =
      loaded_theory_syntax(name) getOrElse overall_syntax

    def node_syntax(nodes: Document.Nodes, name: Document.Node.Name): Outer_Syntax =
      nodes(name).syntax orElse loaded_theory_syntax(name) getOrElse overall_syntax
  }

  sealed case class Deps(sessions_structure: Structure, session_bases: Map[String, Base])
  {
    override def toString: String = "Sessions.Deps(" + sessions_structure + ")"

    def is_empty: Boolean = session_bases.isEmpty
    def apply(name: String): Base = session_bases(name)
    def get(name: String): Option[Base] = session_bases.get(name)

    def imported_sources(name: String): List[SHA1.Digest] =
      session_bases(name).imported_sources.map(_._2)

    def sources(name: String): List[SHA1.Digest] =
      session_bases(name).sources.map(_._2)

    def errors: List[String] =
      (for {
        (name, base) <- session_bases.iterator
        if base.errors.nonEmpty
      } yield cat_lines(base.errors) +
          "\nThe error(s) above occurred in session " + quote(name) + Position.here(base.pos)
      ).toList

    def check_errors: Deps =
      errors match {
        case Nil => this
        case errs => error(cat_lines(errs))
      }
  }

  def deps(sessions_structure: Structure,
      progress: Progress = new Progress,
      inlined_files: Boolean = false,
      verbose: Boolean = false,
      list_files: Boolean = false,
      check_keywords: Set[String] = Set.empty): Deps =
  {
    var cache_sources = Map.empty[JFile, SHA1.Digest]
    def check_sources(paths: List[Path]): List[(Path, SHA1.Digest)] =
    {
      for {
        path <- paths
        file = path.file
        if cache_sources.isDefinedAt(file) || file.isFile
      }
      yield {
        cache_sources.get(file) match {
          case Some(digest) => (path, digest)
          case None =>
            val digest = SHA1.digest(file)
            cache_sources = cache_sources + (file -> digest)
            (path, digest)
        }
      }
    }

    val session_bases =
      sessions_structure.imports_topological_order.foldLeft(Map("" -> sessions_structure.bootstrap)) {
        case (session_bases, session_name) =>
          progress.expose_interrupt()

          val info = sessions_structure(session_name)
          try {
            val deps_base = info.deps_base(session_bases)
            val resources = new Resources(sessions_structure, deps_base)

            if (verbose || list_files) {
              val groups =
                if (info.groups.isEmpty) ""
                else info.groups.mkString(" (", " ", ")")
              progress.echo("Session " + info.chapter_session + groups)
            }

            val dependencies = resources.session_dependencies(info)

            val overall_syntax = dependencies.overall_syntax

            val session_theories =
              dependencies.theories.filter(name => deps_base.theory_qualifier(name) == session_name)

            val theory_files = dependencies.theories.map(_.path)

            dependencies.load_commands

            val (load_commands, load_commands_errors) =
              try { if (inlined_files) (dependencies.load_commands, Nil) else (Nil, Nil) }
              catch { case ERROR(msg) => (Nil, List(msg)) }

            val loaded_files =
              load_commands.map({ case (name, spans) => dependencies.loaded_files(name, spans) })

            val session_files =
              (theory_files ::: loaded_files.flatMap(_._2) :::
                info.document_files.map(file => info.dir + file._1 + file._2)).map(_.expand)

            val imported_files = if (inlined_files) dependencies.imported_files else Nil

            if (list_files)
              progress.echo(cat_lines(session_files.map(_.implode).sorted.map("  " + _)))

            if (check_keywords.nonEmpty) {
              Check_Keywords.check_keywords(
                progress, overall_syntax.keywords, check_keywords, theory_files)
            }

            val session_graph_display: Graph_Display.Graph =
            {
              def session_node(name: String): Graph_Display.Node =
                Graph_Display.Node("[" + name + "]", "session." + name)

              def node(name: Document.Node.Name): Graph_Display.Node =
              {
                val qualifier = deps_base.theory_qualifier(name)
                if (qualifier == info.name)
                  Graph_Display.Node(name.theory_base_name, "theory." + name.theory)
                else session_node(qualifier)
              }

              val required_sessions =
                dependencies.loaded_theories.all_preds(dependencies.theories.map(_.theory))
                  .map(theory => deps_base.theory_qualifier(theory))
                  .filter(name => name != info.name && sessions_structure.defined(name))

              val required_subgraph =
                sessions_structure.imports_graph
                  .restrict(sessions_structure.imports_graph.all_preds(required_sessions).toSet)
                  .transitive_closure
                  .restrict(required_sessions.toSet)
                  .transitive_reduction_acyclic

              val graph0 =
                required_subgraph.topological_order.foldLeft(Graph_Display.empty_graph) {
                  case (g, session) =>
                    val a = session_node(session)
                    val bs = required_subgraph.imm_preds(session).toList.map(session_node)
                    bs.foldLeft((a :: bs).foldLeft(g)(_.default_node(_, Nil)))(_.add_edge(_, a))
                }

              dependencies.entries.foldLeft(graph0) {
                case (g, entry) =>
                  val a = node(entry.name)
                  val bs = entry.header.imports.map(node).filterNot(_ == a)
                  bs.foldLeft((a :: bs).foldLeft(g)(_.default_node(_, Nil)))(_.add_edge(_, a))
              }
            }

            val known_theories =
              dependencies.entries.iterator.map(entry => entry.name.theory -> entry).
                foldLeft(deps_base.known_theories)(_ + _)

            val known_loaded_files = deps_base.known_loaded_files ++ loaded_files

            val import_errors =
            {
              val known_sessions =
                sessions_structure.imports_requirements(List(session_name)).toSet
              for {
                name <- dependencies.theories
                qualifier = deps_base.theory_qualifier(name)
                if !known_sessions(qualifier)
              } yield "Bad import of theory " + quote(name.toString) +
                ": need to include sessions " + quote(qualifier) + " in ROOT"
            }

            val document_errors =
              info.document_theories.flatMap(
              {
                case (thy, pos) =>
                  val parent_sessions =
                    if (sessions_structure.build_graph.defined(session_name)) {
                      sessions_structure.build_requirements(List(session_name))
                    }
                    else Nil

                  def err(msg: String): Option[String] =
                    Some(msg + " " + quote(thy) + Position.here(pos))

                  known_theories.get(thy).map(_.name) match {
                    case None => err("Unknown document theory")
                    case Some(name) =>
                      val qualifier = deps_base.theory_qualifier(name)
                      if (session_theories.contains(name)) {
                        err("Redundant document theory from this session:")
                      }
                      else if (parent_sessions.contains(qualifier)) None
                      else if (dependencies.theories.contains(name)) None
                      else err("Document theory from other session not imported properly:")
                  }
              })
            val document_theories =
              info.document_theories.map({ case (thy, _) => known_theories(thy).name })

            val dir_errors =
            {
              val ok = info.dirs.map(_.canonical_file).toSet
              val bad =
                (for {
                  name <- session_theories.iterator
                  path = name.master_dir_path
                  if !ok(path.canonical_file)
                  path1 = File.relative_path(info.dir.canonical, path).getOrElse(path)
                } yield (path1, name)).toList
              val bad_dirs = (for { (path1, _) <- bad } yield path1.toString).distinct.sorted

              val errs1 =
                for { (path1, name) <- bad }
                yield "Implicit use of directory " + path1 + " for theory " + quote(name.toString)
              val errs2 =
                if (bad_dirs.isEmpty) Nil
                else List("Implicit use of session directories: " + commas(bad_dirs))
              val errs3 = for (p <- info.dirs if !p.is_dir) yield "No such directory: " + p
              val errs4 =
                (for {
                  name <- session_theories.iterator
                  name1 <- resources.find_theory_node(name.theory)
                  if name.node != name1.node
                } yield "Incoherent theory file import:\n  " + name.path + " vs. \n  " + name1.path)
                .toList

              errs1 ::: errs2 ::: errs3 ::: errs4
            }

            val sources_errors =
              for (p <- session_files if !p.is_file) yield "No such file: " + p

            val path_errors =
              try { Path.check_case_insensitive(session_files ::: imported_files); Nil }
              catch { case ERROR(msg) => List(msg) }

            val bibtex_errors =
              try { info.bibtex_entries; Nil }
              catch { case ERROR(msg) => List(msg) }

            val base =
              Base(
                pos = info.pos,
                session_directories = sessions_structure.session_directories,
                global_theories = sessions_structure.global_theories,
                session_theories = session_theories,
                document_theories = document_theories,
                loaded_theories = dependencies.loaded_theories,
                used_theories = dependencies.theories_adjunct,
                load_commands = load_commands.toMap,
                known_theories = known_theories,
                known_loaded_files = known_loaded_files,
                overall_syntax = overall_syntax,
                imported_sources = check_sources(imported_files),
                sources = check_sources(session_files),
                session_graph_display = session_graph_display,
                errors = dependencies.errors ::: load_commands_errors ::: import_errors :::
                  document_errors ::: dir_errors ::: sources_errors ::: path_errors :::
                  bibtex_errors)

            session_bases + (info.name -> base)
          }
          catch {
            case ERROR(msg) =>
              cat_error(msg, "The error(s) above occurred in session " +
                quote(info.name) + Position.here(info.pos))
          }
      }

    Deps(sessions_structure, session_bases)
  }


  /* base info */

  sealed case class Base_Info(
    session: String,
    sessions_structure: Structure,
    errors: List[String],
    base: Base,
    infos: List[Info])
  {
    def check: Base_Info = if (errors.isEmpty) this else error(cat_lines(errors))
  }

  def base_info(options: Options,
    session: String,
    progress: Progress = new Progress,
    dirs: List[Path] = Nil,
    include_sessions: List[String] = Nil,
    session_ancestor: Option[String] = None,
    session_requirements: Boolean = false): Base_Info =
  {
    val full_sessions = load_structure(options, dirs = dirs)

    val selected_sessions =
      full_sessions.selection(Selection(sessions = session :: session_ancestor.toList))
    val info = selected_sessions(session)
    val ancestor = session_ancestor orElse info.parent

    val (session1, infos1) =
      if (session_requirements && ancestor.isDefined) {
        val deps = Sessions.deps(selected_sessions, progress = progress)
        val base = deps(session)

        val ancestor_loaded =
          deps.get(ancestor.get) match {
            case Some(ancestor_base)
            if !selected_sessions.imports_requirements(List(ancestor.get)).contains(session) =>
              ancestor_base.loaded_theories.defined _
            case _ =>
              error("Bad ancestor " + quote(ancestor.get) + " for session " + quote(session))
          }

        val required_theories =
          for {
            thy <- base.loaded_theories.keys
            if !ancestor_loaded(thy) && base.theory_qualifier(thy) != session
          }
          yield thy

        if (required_theories.isEmpty) (ancestor.get, Nil)
        else {
          val other_name = info.name + "_requirements(" + ancestor.get + ")"
          Isabelle_System.isabelle_tmp_prefix()

          (other_name,
            List(
              make_info(info.options,
                dir_selected = false,
                dir = Path.explode("$ISABELLE_TMP_PREFIX"),
                chapter = info.chapter,
                Session_Entry(
                  pos = info.pos,
                  name = other_name,
                  groups = info.groups,
                  path = ".",
                  parent = ancestor,
                  description = "Required theory imports from other sessions",
                  options = Nil,
                  imports = info.deps,
                  directories = Nil,
                  theories = List((Nil, required_theories.map(thy => ((thy, Position.none), false)))),
                  document_theories = Nil,
                  document_files = Nil,
                  export_files = Nil))))
        }
      }
      else (session, Nil)

    val full_sessions1 =
      if (infos1.isEmpty) full_sessions
      else load_structure(options, dirs = dirs, infos = infos1)

    val selected_sessions1 =
      full_sessions1.selection(Selection(sessions = session1 :: session :: include_sessions))

    val deps1 = Sessions.deps(selected_sessions1, progress = progress)

    Base_Info(session1, full_sessions1, deps1.errors, deps1(session1), infos1)
  }


  /* cumulative session info */

  sealed case class Info(
    name: String,
    chapter: String,
    dir_selected: Boolean,
    pos: Position.T,
    groups: List[String],
    dir: Path,
    parent: Option[String],
    description: String,
    directories: List[Path],
    options: Options,
    imports: List[String],
    theories: List[(Options, List[(String, Position.T)])],
    global_theories: List[String],
    document_theories: List[(String, Position.T)],
    document_files: List[(Path, Path)],
    export_files: List[(Path, Int, List[String])],
    meta_digest: SHA1.Digest)
  {
    def chapter_session: String = chapter + "/" + name

    def relative_path(info1: Info): String =
      if (name == info1.name) ""
      else if (chapter == info1.chapter) "../" + info1.name + "/"
      else "../../" + info1.chapter_session + "/"

    def deps: List[String] = parent.toList ::: imports

    def deps_base(session_bases: String => Base): Base =
    {
      val parent_base = session_bases(parent.getOrElse(""))
      val imports_bases = imports.map(session_bases)
      parent_base.copy(
        known_theories =
          (for {
            base <- imports_bases.iterator
            (_, entry) <- base.known_theories.iterator
          } yield (entry.name.theory -> entry)).foldLeft(parent_base.known_theories)(_ + _),
        known_loaded_files =
          imports_bases.iterator.map(_.known_loaded_files).
            foldLeft(parent_base.known_loaded_files)(_ ++ _))
    }

    def dirs: List[Path] = dir :: directories

    def timeout_ignored: Boolean =
      !options.bool("timeout_build") || Time.seconds(options.real("timeout")) < Time.ms(1)

    def timeout: Time = Time.seconds(options.real("timeout") * options.real("timeout_scale"))

    def document_enabled: Boolean =
      options.string("document") match {
        case "" | "false" => false
        case "pdf" => true
        case doc => error("Bad document specification " + quote(doc))
      }

    def document_variants: List[Document_Build.Document_Variant] =
    {
      val variants =
        Library.space_explode(':', options.string("document_variants")).
          map(Document_Build.Document_Variant.parse)

      val dups = Library.duplicates(variants.map(_.name))
      if (dups.nonEmpty) error("Duplicate document variants: " + commas_quote(dups))

      variants
    }

    def documents: List[Document_Build.Document_Variant] =
    {
      val variants = document_variants
      if (!document_enabled || document_files.isEmpty) Nil else variants
    }

    def document_output: Option[Path] =
      options.string("document_output") match {
        case "" => None
        case s => Some(dir + Path.explode(s))
      }

    def browser_info: Boolean = options.bool("browser_info")

    lazy val bibtex_entries: List[Text.Info[String]] =
      (for {
        (document_dir, file) <- document_files.iterator
        if Bibtex.is_bibtex(file.file_name)
        info <- Bibtex.entries(File.read(dir + document_dir + file)).iterator
      } yield info).toList

    def record_proofs: Boolean = options.int("record_proofs") >= 2

    def is_afp: Boolean = chapter == AFP.chapter
    def is_afp_bulky: Boolean = is_afp && groups.exists(AFP.groups_bulky.contains)
  }

  def make_info(options: Options, dir_selected: Boolean, dir: Path, chapter: String,
    entry: Session_Entry): Info =
  {
    try {
      val name = entry.name

      if (exclude_session(name)) error("Bad session name")
      if (is_pure(name) && entry.parent.isDefined) error("Illegal parent session")
      if (!is_pure(name) && !entry.parent.isDefined) error("Missing parent session")

      val session_path = dir + Path.explode(entry.path)
      val directories = entry.directories.map(dir => session_path + Path.explode(dir))

      val session_options = options ++ entry.options

      val theories =
        entry.theories.map({ case (opts, thys) =>
          (session_options ++ opts,
            thys.map({ case ((thy, pos), _) =>
              if (exclude_theory(thy))
                error("Bad theory name " + quote(thy) + Position.here(pos))
              else (thy, pos) })) })

      val global_theories =
        for { (_, thys) <- entry.theories; ((thy, pos), global) <- thys if global }
        yield {
          val thy_name = Path.explode(thy).file_name
          if (Long_Name.is_qualified(thy_name))
            error("Bad qualified name for global theory " +
              quote(thy_name) + Position.here(pos))
          else thy_name
        }

      val conditions =
        theories.flatMap(thys => space_explode(',', thys._1.string("condition"))).distinct.sorted.
          map(x => (x, Isabelle_System.getenv(x) != ""))

      val document_files =
        entry.document_files.map({ case (s1, s2) => (Path.explode(s1), Path.explode(s2)) })

      val export_files =
        entry.export_files.map({ case (dir, prune, pats) => (Path.explode(dir), prune, pats) })

      val meta_digest =
        SHA1.digest(
          (name, chapter, entry.parent, entry.directories, entry.options, entry.imports,
            entry.theories_no_position, conditions, entry.document_theories_no_position,
            entry.document_files)
          .toString)

      Info(name, chapter, dir_selected, entry.pos, entry.groups, session_path,
        entry.parent, entry.description, directories, session_options,
        entry.imports, theories, global_theories, entry.document_theories, document_files,
        export_files, meta_digest)
    }
    catch {
      case ERROR(msg) =>
        error(msg + "\nThe error(s) above occurred in session entry " +
          quote(entry.name) + Position.here(entry.pos))
    }
  }

  object Selection
  {
    val empty: Selection = Selection()
    val all: Selection = Selection(all_sessions = true)
    def session(session: String): Selection = Selection(sessions = List(session))
  }

  sealed case class Selection(
    requirements: Boolean = false,
    all_sessions: Boolean = false,
    base_sessions: List[String] = Nil,
    exclude_session_groups: List[String] = Nil,
    exclude_sessions: List[String] = Nil,
    session_groups: List[String] = Nil,
    sessions: List[String] = Nil)
  {
    def ++ (other: Selection): Selection =
      Selection(
        requirements = requirements || other.requirements,
        all_sessions = all_sessions || other.all_sessions,
        base_sessions = Library.merge(base_sessions, other.base_sessions),
        exclude_session_groups = Library.merge(exclude_session_groups, other.exclude_session_groups),
        exclude_sessions = Library.merge(exclude_sessions, other.exclude_sessions),
        session_groups = Library.merge(session_groups, other.session_groups),
        sessions = Library.merge(sessions, other.sessions))
  }

  object Structure
  {
    val empty: Structure = make(Nil)

    def make(infos: List[Info]): Structure =
    {
      def add_edges(graph: Graph[String, Info], kind: String, edges: Info => Iterable[String])
        : Graph[String, Info] =
      {
        def add_edge(pos: Position.T, name: String, g: Graph[String, Info], parent: String) =
        {
          if (!g.defined(parent))
            error("Bad " + kind + " session " + quote(parent) + " for " +
              quote(name) + Position.here(pos))

          try { g.add_edge_acyclic(parent, name) }
          catch {
            case exn: Graph.Cycles[_] =>
              error(cat_lines(exn.cycles.map(cycle =>
                "Cyclic session dependency of " +
                  cycle.map(c => quote(c.toString)).mkString(" via "))) + Position.here(pos))
          }
        }
        graph.iterator.foldLeft(graph) {
          case (g, (name, (info, _))) =>
            edges(info).foldLeft(g)(add_edge(info.pos, name, _, _))
        }
      }

      val info_graph =
        infos.foldLeft(Graph.string[Info]) {
          case (graph, info) =>
            if (graph.defined(info.name))
              error("Duplicate session " + quote(info.name) + Position.here(info.pos) +
                Position.here(graph.get_node(info.name).pos))
            else graph.new_node(info.name, info)
        }
      val build_graph = add_edges(info_graph, "parent", _.parent)
      val imports_graph = add_edges(build_graph, "imports", _.imports)

      val session_positions: List[(String, Position.T)] =
        (for ((name, (info, _)) <- info_graph.iterator) yield (name, info.pos)).toList

      val session_directories: Map[JFile, String] =
        (for {
          session <- imports_graph.topological_order.iterator
          info = info_graph.get_node(session)
          dir <- info.dirs.iterator
        } yield (info, dir)).foldLeft(Map.empty[JFile, String]) {
            case (dirs, (info, dir)) =>
              val session = info.name
              val canonical_dir = dir.canonical_file
              dirs.get(canonical_dir) match {
                case Some(session1) =>
                  val info1 = info_graph.get_node(session1)
                  error("Duplicate use of directory " + dir +
                    "\n  for session " + quote(session1) + Position.here(info1.pos) +
                    "\n  vs. session " + quote(session) + Position.here(info.pos))
                case None => dirs + (canonical_dir -> session)
              }
          }

      val global_theories: Map[String, String] =
        (for {
          session <- imports_graph.topological_order.iterator
          info = info_graph.get_node(session)
          thy <- info.global_theories.iterator }
          yield (info, thy)).foldLeft(Thy_Header.bootstrap_global_theories.toMap) {
            case (global, (info, thy)) =>
              val qualifier = info.name
              global.get(thy) match {
                case Some(qualifier1) if qualifier != qualifier1 =>
                  error("Duplicate global theory " + quote(thy) + Position.here(info.pos))
                case _ => global + (thy -> qualifier)
              }
          }

      new Structure(
        session_positions, session_directories, global_theories, build_graph, imports_graph)
    }
  }

  final class Structure private[Sessions](
      val session_positions: List[(String, Position.T)],
      val session_directories: Map[JFile, String],
      val global_theories: Map[String, String],
      val build_graph: Graph[String, Info],
      val imports_graph: Graph[String, Info])
  {
    sessions_structure =>

    def bootstrap: Base =
      Base(
        session_directories = session_directories,
        global_theories = global_theories,
        overall_syntax = Thy_Header.bootstrap_syntax)

    def dest_session_directories: List[(String, String)] =
      for ((file, session) <- session_directories.toList)
        yield (File.standard_path(file), session)

    lazy val chapters: SortedMap[String, List[Info]] =
      build_graph.iterator.foldLeft(SortedMap.empty[String, List[Info]]) {
        case (chs, (_, (info, _))) =>
          chs + (info.chapter -> (info :: chs.getOrElse(info.chapter, Nil)))
      }

    def build_graph_display: Graph_Display.Graph = Graph_Display.make_graph(build_graph)
    def imports_graph_display: Graph_Display.Graph = Graph_Display.make_graph(imports_graph)

    def defined(name: String): Boolean = imports_graph.defined(name)
    def apply(name: String): Info = imports_graph.get_node(name)
    def get(name: String): Option[Info] = if (defined(name)) Some(apply(name)) else None

    def theory_qualifier(name: String): String =
      global_theories.getOrElse(name, Long_Name.qualifier(name))

    def check_sessions(names: List[String]): Unit =
    {
      val bad_sessions = SortedSet(names.filterNot(defined): _*).toList
      if (bad_sessions.nonEmpty)
        error("Undefined session(s): " + commas_quote(bad_sessions))
    }

    def check_sessions(sel: Selection): Unit =
      check_sessions(sel.base_sessions ::: sel.exclude_sessions ::: sel.sessions)

    private def selected(graph: Graph[String, Info], sel: Selection): List[String] =
    {
      check_sessions(sel)

      val select_group = sel.session_groups.toSet
      val select_session = sel.sessions.toSet ++ imports_graph.all_succs(sel.base_sessions)

      val selected0 =
        if (sel.all_sessions) graph.keys
        else {
          (for {
            (name, (info, _)) <- graph.iterator
            if info.dir_selected || select_session(name) ||
              graph.get_node(name).groups.exists(select_group)
          } yield name).toList
        }

      if (sel.requirements) (graph.all_preds(selected0).toSet -- selected0).toList
      else selected0
    }

    def selection(sel: Selection): Structure =
    {
      check_sessions(sel)

      val excluded =
      {
        val exclude_group = sel.exclude_session_groups.toSet
        val exclude_group_sessions =
          (for {
            (name, (info, _)) <- imports_graph.iterator
            if imports_graph.get_node(name).groups.exists(exclude_group)
          } yield name).toList
        imports_graph.all_succs(exclude_group_sessions ::: sel.exclude_sessions).toSet
      }

      def restrict(graph: Graph[String, Info]): Graph[String, Info] =
      {
        val sessions = graph.all_preds(selected(graph, sel)).filterNot(excluded)
        graph.restrict(graph.all_preds(sessions).toSet)
      }

      new Structure(
        session_positions, session_directories, global_theories,
        restrict(build_graph), restrict(imports_graph))
    }

    def selection(session: String): Structure = selection(Selection.session(session))

    def selection_deps(
      selection: Selection,
      progress: Progress = new Progress,
      loading_sessions: Boolean = false,
      inlined_files: Boolean = false,
      verbose: Boolean = false): Deps =
    {
      val deps =
        Sessions.deps(sessions_structure.selection(selection),
          progress = progress, inlined_files = inlined_files, verbose = verbose)

      if (loading_sessions) {
        val selection_size = deps.sessions_structure.build_graph.size
        if (selection_size > 1) progress.echo("Loading " + selection_size + " sessions ...")
      }

      deps
    }

    def hierarchy(session: String): List[String] = build_graph.all_preds(List(session))

    def build_selection(sel: Selection): List[String] = selected(build_graph, sel)
    def build_descendants(ss: List[String]): List[String] = build_graph.all_succs(ss)
    def build_requirements(ss: List[String]): List[String] = build_graph.all_preds_rev(ss)
    def build_topological_order: List[String] = build_graph.topological_order

    def imports_selection(sel: Selection): List[String] = selected(imports_graph, sel)
    def imports_descendants(ss: List[String]): List[String] = imports_graph.all_succs(ss)
    def imports_requirements(ss: List[String]): List[String] = imports_graph.all_preds_rev(ss)
    def imports_topological_order: List[String] = imports_graph.topological_order

    def bibtex_entries: List[(String, List[String])] =
      build_topological_order.flatMap(name =>
        apply(name).bibtex_entries match {
          case Nil => None
          case entries => Some(name -> entries.map(_.info))
        })

    def session_chapters: List[(String, String)] =
      imports_topological_order.map(name => name -> apply(name).chapter)

    override def toString: String =
      imports_graph.keys_iterator.mkString("Sessions.Structure(", ", ", ")")
  }


  /* parser */

  private val CHAPTER = "chapter"
  private val SESSION = "session"
  private val IN = "in"
  private val DESCRIPTION = "description"
  private val DIRECTORIES = "directories"
  private val OPTIONS = "options"
  private val SESSIONS = "sessions"
  private val THEORIES = "theories"
  private val GLOBAL = "global"
  private val DOCUMENT_THEORIES = "document_theories"
  private val DOCUMENT_FILES = "document_files"
  private val EXPORT_FILES = "export_files"

  val root_syntax: Outer_Syntax =
    Outer_Syntax.empty + "(" + ")" + "+" + "," + "=" + "[" + "]" +
      GLOBAL + IN +
      (CHAPTER, Keyword.THY_DECL) +
      (SESSION, Keyword.THY_DECL) +
      (DESCRIPTION, Keyword.QUASI_COMMAND) +
      (DIRECTORIES, Keyword.QUASI_COMMAND) +
      (OPTIONS, Keyword.QUASI_COMMAND) +
      (SESSIONS, Keyword.QUASI_COMMAND) +
      (THEORIES, Keyword.QUASI_COMMAND) +
      (DOCUMENT_THEORIES, Keyword.QUASI_COMMAND) +
      (DOCUMENT_FILES, Keyword.QUASI_COMMAND) +
      (EXPORT_FILES, Keyword.QUASI_COMMAND)

  abstract class Entry
  sealed case class Chapter(name: String) extends Entry
  sealed case class Session_Entry(
    pos: Position.T,
    name: String,
    groups: List[String],
    path: String,
    parent: Option[String],
    description: String,
    options: List[Options.Spec],
    imports: List[String],
    directories: List[String],
    theories: List[(List[Options.Spec], List[((String, Position.T), Boolean)])],
    document_theories: List[(String, Position.T)],
    document_files: List[(String, String)],
    export_files: List[(String, Int, List[String])]) extends Entry
  {
    def theories_no_position: List[(List[Options.Spec], List[(String, Boolean)])] =
      theories.map({ case (a, b) => (a, b.map({ case ((c, _), d) => (c, d) })) })
    def document_theories_no_position: List[String] =
      document_theories.map(_._1)
  }

  private object Parser extends Options.Parser
  {
    private val chapter: Parser[Chapter] =
    {
      val chapter_name = atom("chapter name", _.is_name)

      command(CHAPTER) ~! chapter_name ^^ { case _ ~ a => Chapter(a) }
    }

    private val session_entry: Parser[Session_Entry] =
    {
      val option =
        option_name ~ opt($$$("=") ~! option_value ^^ { case _ ~ x => x }) ^^
          { case x ~ y => (x, y) }
      val options = $$$("[") ~> rep1sep(option, $$$(",")) <~ $$$("]")

      val theory_entry =
        position(theory_name) ~ opt_keyword(GLOBAL) ^^ { case x ~ y => (x, y) }

      val theories =
        $$$(THEORIES) ~!
          ((options | success(Nil)) ~ rep1(theory_entry)) ^^
          { case _ ~ (x ~ y) => (x, y) }

      val in_path = $$$("(") ~! ($$$(IN) ~ path ~ $$$(")")) ^^ { case _ ~ (_ ~ x ~ _) => x }

      val document_theories =
        $$$(DOCUMENT_THEORIES) ~! rep1(position(name)) ^^ { case _ ~ x => x }

      val document_files =
        $$$(DOCUMENT_FILES) ~!
          ((in_path | success("document")) ~ rep1(path)) ^^ { case _ ~ (x ~ y) => y.map((x, _)) }

      val prune = $$$("[") ~! (nat ~ $$$("]")) ^^ { case _ ~ (x ~ _) => x } | success(0)

      val export_files =
        $$$(EXPORT_FILES) ~! ((in_path | success("export")) ~ prune ~ rep1(embedded)) ^^
          { case _ ~ (x ~ y ~ z) => (x, y, z) }

      command(SESSION) ~!
        (position(session_name) ~
          (($$$("(") ~! (rep1(name) <~ $$$(")")) ^^ { case _ ~ x => x }) | success(Nil)) ~
          (($$$(IN) ~! path ^^ { case _ ~ x => x }) | success(".")) ~
          ($$$("=") ~!
            (opt(session_name ~! $$$("+") ^^ { case x ~ _ => x }) ~
              (($$$(DESCRIPTION) ~! text ^^ { case _ ~ x => x }) | success("")) ~
              (($$$(OPTIONS) ~! options ^^ { case _ ~ x => x }) | success(Nil)) ~
              (($$$(SESSIONS) ~! rep1(session_name)  ^^ { case _ ~ x => x }) | success(Nil)) ~
              (($$$(DIRECTORIES) ~! rep1(path) ^^ { case _ ~ x => x }) | success(Nil)) ~
              rep(theories) ~
              (opt(document_theories) ^^ (x => x.getOrElse(Nil))) ~
              (rep(document_files) ^^ (x => x.flatten)) ~
              rep(export_files)))) ^^
        { case _ ~ ((a, pos) ~ b ~ c ~ (_ ~ (d ~ e ~ f ~ g ~ h ~ i ~ j ~ k ~ l))) =>
            Session_Entry(pos, a, b, c, d, e, f, g, h, i, j, k, l) }
    }

    def parse_root(path: Path): List[Entry] =
    {
      val toks = Token.explode(root_syntax.keywords, File.read(path))
      val start = Token.Pos.file(path.implode)

      parse_all(rep(chapter | session_entry), Token.reader(toks, start)) match {
        case Success(result, _) => result
        case bad => error(bad.toString)
      }
    }
  }

  def parse_root(path: Path): List[Entry] = Parser.parse_root(path)

  def parse_root_entries(path: Path): List[Session_Entry] =
    for (entry <- Parser.parse_root(path) if entry.isInstanceOf[Session_Entry])
    yield entry.asInstanceOf[Session_Entry]

  def read_root(options: Options, select: Boolean, path: Path): List[Info] =
  {
    var entry_chapter = UNSORTED
    val infos = new mutable.ListBuffer[Info]
    parse_root(path).foreach {
      case Chapter(name) => entry_chapter = name
      case entry: Session_Entry =>
        infos += make_info(options, select, path.dir, entry_chapter, entry)
    }
    infos.toList
  }

  def parse_roots(roots: Path): List[String] =
  {
    for {
      line <- split_lines(File.read(roots))
      if !(line == "" || line.startsWith("#"))
    } yield line
  }


  /* load sessions from certain directories */

  def is_session_dir(dir: Path): Boolean =
    (dir + ROOT).is_file || (dir + ROOTS).is_file

  private def check_session_dir(dir: Path): Path =
    if (is_session_dir(dir)) File.pwd() + dir.expand
    else error("Bad session root directory (missing ROOT or ROOTS): " + dir.expand.toString)

  def directories(dirs: List[Path], select_dirs: List[Path]): List[(Boolean, Path)] =
  {
    val default_dirs = Components.directories().filter(is_session_dir)
    for { (select, dir) <- (default_dirs ::: dirs).map((false, _)) ::: select_dirs.map((true, _)) }
    yield (select, dir.canonical)
  }

  def load_structure(options: Options,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    infos: List[Info] = Nil): Structure =
  {
    def load_dir(select: Boolean, dir: Path): List[(Boolean, Path)] =
      load_root(select, dir) ::: load_roots(select, dir)

    def load_root(select: Boolean, dir: Path): List[(Boolean, Path)] =
    {
      val root = dir + ROOT
      if (root.is_file) List((select, root)) else Nil
    }

    def load_roots(select: Boolean, dir: Path): List[(Boolean, Path)] =
    {
      val roots = dir + ROOTS
      if (roots.is_file) {
        for {
          entry <- parse_roots(roots)
          dir1 =
            try { check_session_dir(dir + Path.explode(entry)) }
            catch {
              case ERROR(msg) =>
                error(msg + "\nThe error(s) above occurred in session catalog " + roots.toString)
            }
          res <- load_dir(select, dir1)
        } yield res
      }
      else Nil
    }

    val roots =
      for {
        (select, dir) <- directories(dirs, select_dirs)
        res <- load_dir(select, check_session_dir(dir))
      } yield res

    val unique_roots =
      roots.foldLeft(Map.empty[JFile, (Boolean, Path)]) {
        case (m, (select, path)) =>
          val file = path.canonical_file
          m.get(file) match {
            case None => m + (file -> (select, path))
            case Some((select1, path1)) => m + (file -> (select1 || select, path1))
          }
      }.toList.map(_._2)

    Structure.make(unique_roots.flatMap(p => read_root(options, p._1, p._2)) ::: infos)
  }


  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("sessions", "explore structure of Isabelle sessions",
    Scala_Project.here, args =>
  {
    var base_sessions: List[String] = Nil
    var select_dirs: List[Path] = Nil
    var requirements = false
    var exclude_session_groups: List[String] = Nil
    var all_sessions = false
    var dirs: List[Path] = Nil
    var session_groups: List[String] = Nil
    var exclude_sessions: List[String] = Nil

    val getopts = Getopts("""
Usage: isabelle sessions [OPTIONS] [SESSIONS ...]

  Options are:
    -B NAME      include session NAME and all descendants
    -D DIR       include session directory and select its sessions
    -R           refer to requirements of selected sessions
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -d DIR       include session directory
    -g NAME      select session group NAME
    -x NAME      exclude session NAME and all descendants

  Explore the structure of Isabelle sessions and print result names in
  topological order (on stdout).
""",
      "B:" -> (arg => base_sessions = base_sessions ::: List(arg)),
      "D:" -> (arg => select_dirs = select_dirs ::: List(Path.explode(arg))),
      "R" -> (_ => requirements = true),
      "X:" -> (arg => exclude_session_groups = exclude_session_groups ::: List(arg)),
      "a" -> (_ => all_sessions = true),
      "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
      "g:" -> (arg => session_groups = session_groups ::: List(arg)),
      "x:" -> (arg => exclude_sessions = exclude_sessions ::: List(arg)))

    val sessions = getopts(args)

    val options = Options.init()

    val selection =
      Selection(requirements = requirements, all_sessions = all_sessions, base_sessions = base_sessions,
        exclude_session_groups = exclude_session_groups, exclude_sessions = exclude_sessions,
        session_groups = session_groups, sessions = sessions)
    val sessions_structure =
      load_structure(options, dirs = dirs, select_dirs = select_dirs).selection(selection)

    for (name <- sessions_structure.imports_topological_order) {
      Output.writeln(name, stdout = true)
    }
  })



  /** heap file with SHA1 digest **/

  private val sha1_prefix = "SHA1:"

  def read_heap_digest(heap: Path): Option[String] =
  {
    if (heap.is_file) {
      using(FileChannel.open(heap.file.toPath, StandardOpenOption.READ))(file =>
      {
        val len = file.size
        val n = sha1_prefix.length + SHA1.digest_length
        if (len >= n) {
          file.position(len - n)

          val buf = ByteBuffer.allocate(n)
          var i = 0
          var m = 0
          do {
            m = file.read(buf)
            if (m != -1) i += m
          }
          while (m != -1 && n > i)

          if (i == n) {
            val prefix = new String(buf.array(), 0, sha1_prefix.length, UTF8.charset)
            val s = new String(buf.array(), sha1_prefix.length, SHA1.digest_length, UTF8.charset)
            if (prefix == sha1_prefix) Some(s) else None
          }
          else None
        }
        else None
      })
    }
    else None
  }

  def write_heap_digest(heap: Path): String =
    read_heap_digest(heap) match {
      case None =>
        val s = SHA1.digest(heap).rep
        File.append(heap, sha1_prefix + s)
        s
      case Some(s) => s
    }



  /** persistent store **/

  object Session_Info
  {
    val session_name = SQL.Column.string("session_name").make_primary_key

    // Build_Log.Session_Info
    val session_timing = SQL.Column.bytes("session_timing")
    val command_timings = SQL.Column.bytes("command_timings")
    val theory_timings = SQL.Column.bytes("theory_timings")
    val ml_statistics = SQL.Column.bytes("ml_statistics")
    val task_statistics = SQL.Column.bytes("task_statistics")
    val errors = SQL.Column.bytes("errors")
    val build_log_columns =
      List(session_name, session_timing, command_timings, theory_timings,
        ml_statistics, task_statistics, errors)

    // Build.Session_Info
    val sources = SQL.Column.string("sources")
    val input_heaps = SQL.Column.string("input_heaps")
    val output_heap = SQL.Column.string("output_heap")
    val return_code = SQL.Column.int("return_code")
    val build_columns = List(sources, input_heaps, output_heap, return_code)

    val table = SQL.Table("isabelle_session_info", build_log_columns ::: build_columns)
  }

  class Database_Context private[Sessions](
    val store: Sessions.Store,
    database_server: Option[SQL.Database]) extends AutoCloseable
  {
    def cache: XML.Cache = store.cache

    def close(): Unit = database_server.foreach(_.close())

    def output_database[A](session: String)(f: SQL.Database => A): A =
      database_server match {
        case Some(db) => f(db)
        case None => using(store.open_database(session, output = true))(f)
      }

    def input_database[A](session: String)(f: (SQL.Database, String) => Option[A]): Option[A] =
      database_server match {
        case Some(db) => f(db, session)
        case None =>
          store.try_open_database(session) match {
            case Some(db) => using(db)(f(_, session))
            case None => None
          }
      }

    def read_export(
      sessions: List[String], theory_name: String, name: String): Option[Export.Entry] =
    {
      val attempts =
        database_server match {
          case Some(db) =>
            sessions.view.map(session_name =>
              Export.read_entry(db, store.cache, session_name, theory_name, name))
          case None =>
            sessions.view.map(session_name =>
              store.try_open_database(session_name) match {
                case Some(db) =>
                  using(db)(Export.read_entry(_, store.cache, session_name, theory_name, name))
                case None => None
              })
        }
      attempts.collectFirst({ case Some(entry) => entry })
    }

    def get_export(
        session_hierarchy: List[String], theory_name: String, name: String): Export.Entry =
      read_export(session_hierarchy, theory_name, name) getOrElse
        Export.empty_entry(theory_name, name)

    override def toString: String =
    {
      val s =
        database_server match {
          case Some(db) => db.toString
          case None => "input_dirs = " + store.input_dirs.map(_.absolute).mkString(", ")
        }
      "Database_Context(" + s + ")"
    }
  }

  def store(options: Options, cache: XML.Cache = XML.Cache.make()): Store =
    new Store(options, cache)

  class Store private[Sessions](val options: Options, val cache: XML.Cache)
  {
    store =>

    override def toString: String = "Store(output_dir = " + output_dir.absolute + ")"


    /* directories */

    val system_output_dir: Path = Path.explode("$ISABELLE_HEAPS_SYSTEM/$ML_IDENTIFIER")
    val user_output_dir: Path = Path.explode("$ISABELLE_HEAPS/$ML_IDENTIFIER")

    def system_heaps: Boolean = options.bool("system_heaps")

    val output_dir: Path =
      if (system_heaps) system_output_dir else user_output_dir

    val input_dirs: List[Path] =
      if (system_heaps) List(system_output_dir)
      else List(user_output_dir, system_output_dir)

    def presentation_dir: Path =
      if (system_heaps) Path.explode("$ISABELLE_BROWSER_INFO_SYSTEM")
      else Path.explode("$ISABELLE_BROWSER_INFO")


    /* file names */

    def heap(name: String): Path = Path.basic(name)
    def database(name: String): Path = Path.basic("log") + Path.basic(name).ext("db")
    def log(name: String): Path = Path.basic("log") + Path.basic(name)
    def log_gz(name: String): Path = log(name).ext("gz")

    def output_heap(name: String): Path = output_dir + heap(name)
    def output_database(name: String): Path = output_dir + database(name)
    def output_log(name: String): Path = output_dir + log(name)
    def output_log_gz(name: String): Path = output_dir + log_gz(name)

    def prepare_output_dir(): Unit = Isabelle_System.make_directory(output_dir + Path.basic("log"))


    /* heap */

    def find_heap(name: String): Option[Path] =
      input_dirs.map(_ + heap(name)).find(_.is_file)

    def find_heap_digest(name: String): Option[String] =
      find_heap(name).flatMap(read_heap_digest)

    def the_heap(name: String): Path =
      find_heap(name) getOrElse
        error("Missing heap image for session " + quote(name) + " -- expected in:\n" +
          cat_lines(input_dirs.map(dir => "  " + dir.expand.implode)))


    /* database */

    def database_server: Boolean = options.bool("build_database_server")

    def open_database_server(): SQL.Database =
      PostgreSQL.open_database(
        user = options.string("build_database_user"),
        password = options.string("build_database_password"),
        database = options.string("build_database_name"),
        host = options.string("build_database_host"),
        port = options.int("build_database_port"),
        ssh =
          options.proper_string("build_database_ssh_host").map(ssh_host =>
            SSH.open_session(options,
              host = ssh_host,
              user = options.string("build_database_ssh_user"),
              port = options.int("build_database_ssh_port"))),
        ssh_close = true)

    def open_database_context(): Database_Context =
      new Database_Context(store, if (database_server) Some(open_database_server()) else None)

    def try_open_database(name: String, output: Boolean = false): Option[SQL.Database] =
    {
      def check(db: SQL.Database): Option[SQL.Database] =
        if (output || session_info_exists(db)) Some(db) else { db.close(); None }

      if (database_server) check(open_database_server())
      else if (output) Some(SQLite.open_database(output_database(name)))
      else {
        (for {
          dir <- input_dirs.view
          path = dir + database(name) if path.is_file
          db <- check(SQLite.open_database(path))
        } yield db).headOption
      }
    }

    def open_database(name: String, output: Boolean = false): SQL.Database =
      try_open_database(name, output = output) getOrElse
        error("Missing build database for session " + quote(name))

    def clean_output(name: String): (Boolean, Boolean) =
    {
      val relevant_db =
        database_server &&
        {
          try_open_database(name) match {
            case Some(db) =>
              try {
                db.transaction {
                  val relevant_db = session_info_defined(db, name)
                  init_session_info(db, name)
                  relevant_db
                }
              } finally { db.close() }
            case None => false
          }
        }

      val del =
        for {
          dir <-
            (if (system_heaps) List(user_output_dir, system_output_dir) else List(user_output_dir))
          file <- List(heap(name), database(name), log(name), log_gz(name))
          path = dir + file if path.is_file
        } yield path.file.delete

      val relevant = relevant_db || del.nonEmpty
      val ok = del.forall(b => b)
      (relevant, ok)
    }


    /* SQL database content */

    def read_bytes(db: SQL.Database, name: String, column: SQL.Column): Bytes =
      db.using_statement(Session_Info.table.select(List(column),
        Session_Info.session_name.where_equal(name)))(stmt =>
      {
        val res = stmt.execute_query()
        if (!res.next()) Bytes.empty else res.bytes(column)
      })

    def read_properties(db: SQL.Database, name: String, column: SQL.Column): List[Properties.T] =
      Properties.uncompress(read_bytes(db, name, column), cache = cache)


    /* session info */

    def init_session_info(db: SQL.Database, name: String): Unit =
    {
      db.transaction {
        db.create_table(Session_Info.table)
        db.using_statement(
          Session_Info.table.delete(Session_Info.session_name.where_equal(name)))(_.execute())

        db.create_table(Export.Data.table)
        db.using_statement(
          Export.Data.table.delete(Export.Data.session_name.where_equal(name)))(_.execute())

        db.create_table(Document_Build.Data.table)
        db.using_statement(
          Document_Build.Data.table.delete(
            Document_Build.Data.session_name.where_equal(name)))(_.execute())
      }
    }

    def session_info_exists(db: SQL.Database): Boolean =
    {
      val tables = db.tables
      tables.contains(Session_Info.table.name) &&
      tables.contains(Export.Data.table.name)
    }

    def session_info_defined(db: SQL.Database, name: String): Boolean =
      db.transaction {
        session_info_exists(db) &&
        {
          db.using_statement(
            Session_Info.table.select(List(Session_Info.session_name),
              Session_Info.session_name.where_equal(name)))(stmt => stmt.execute_query().next())
        }
      }

    def write_session_info(
      db: SQL.Database,
      name: String,
      build_log: Build_Log.Session_Info,
      build: Build.Session_Info): Unit =
    {
      db.transaction {
        db.using_statement(Session_Info.table.insert())(stmt =>
        {
          stmt.string(1) = name
          stmt.bytes(2) = Properties.encode(build_log.session_timing)
          stmt.bytes(3) = Properties.compress(build_log.command_timings, cache = cache.xz)
          stmt.bytes(4) = Properties.compress(build_log.theory_timings, cache = cache.xz)
          stmt.bytes(5) = Properties.compress(build_log.ml_statistics, cache = cache.xz)
          stmt.bytes(6) = Properties.compress(build_log.task_statistics, cache = cache.xz)
          stmt.bytes(7) = Build_Log.compress_errors(build_log.errors, cache = cache.xz)
          stmt.string(8) = build.sources
          stmt.string(9) = cat_lines(build.input_heaps)
          stmt.string(10) = build.output_heap getOrElse ""
          stmt.int(11) = build.return_code
          stmt.execute()
        })
      }
    }

    def read_session_timing(db: SQL.Database, name: String): Properties.T =
      Properties.decode(read_bytes(db, name, Session_Info.session_timing), cache = cache)

    def read_command_timings(db: SQL.Database, name: String): List[Properties.T] =
      read_properties(db, name, Session_Info.command_timings)

    def read_theory_timings(db: SQL.Database, name: String): List[Properties.T] =
      read_properties(db, name, Session_Info.theory_timings)

    def read_ml_statistics(db: SQL.Database, name: String): List[Properties.T] =
      read_properties(db, name, Session_Info.ml_statistics)

    def read_task_statistics(db: SQL.Database, name: String): List[Properties.T] =
      read_properties(db, name, Session_Info.task_statistics)

    def read_theories(db: SQL.Database, name: String): List[String] =
      read_theory_timings(db, name).flatMap(Markup.Name.unapply)

    def read_errors(db: SQL.Database, name: String): List[String] =
      Build_Log.uncompress_errors(read_bytes(db, name, Session_Info.errors), cache = cache)

    def read_build(db: SQL.Database, name: String): Option[Build.Session_Info] =
    {
      if (db.tables.contains(Session_Info.table.name)) {
        db.using_statement(Session_Info.table.select(Session_Info.build_columns,
          Session_Info.session_name.where_equal(name)))(stmt =>
        {
          val res = stmt.execute_query()
          if (!res.next()) None
          else {
            Some(
              Build.Session_Info(
                res.string(Session_Info.sources),
                split_lines(res.string(Session_Info.input_heaps)),
                res.string(Session_Info.output_heap) match { case "" => None case s => Some(s) },
                res.int(Session_Info.return_code)))
          }
        })
      }
      else None
    }
  }
}
