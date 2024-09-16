/*  Title:      Pure/Build/sessions.scala
    Author:     Makarius

Cumulative session information.
*/

package isabelle

import java.io.{File => JFile}

import scala.collection.immutable.{SortedSet, SortedMap}
import scala.collection.mutable


object Sessions {
  /* main operations */

  def background0(session: String): Background = Background.empty(session)

  def background(options: Options,
    session: String,
    progress: Progress = new Progress,
    dirs: List[Path] = Nil,
    include_sessions: List[String] = Nil,
    session_ancestor: Option[String] = None,
    session_requirements: Boolean = false
  ): Background = {
    Background.load(options, session, progress = progress, dirs = dirs,
      include_sessions = include_sessions, session_ancestor = session_ancestor,
      session_requirements = session_requirements)
  }

  def load_structure(
    options: Options,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    infos: List[Info] = Nil,
    augment_options: String => List[Options.Spec] = _ => Nil
  ): Structure = {
    val roots = load_root_files(dirs = dirs, select_dirs = select_dirs)
    Structure.make(options, augment_options, roots = roots, infos = infos)
  }

  def deps(sessions_structure: Structure,
    progress: Progress = new Progress,
    inlined_files: Boolean = false,
    list_files: Boolean = false
  ): Deps = {
    Deps.load(sessions_structure, progress = progress, inlined_files = inlined_files,
      list_files = list_files)
  }


  /* session and theory names */

  val ROOTS: Path = Path.explode("ROOTS")
  val ROOT: Path = Path.explode("ROOT")

  val roots_name: String = "ROOTS"
  val root_name: String = "ROOT"
  val theory_import: String = "Pure.Sessions"

  val UNSORTED = "Unsorted"
  val DRAFT = "Draft"

  def is_pure(name: String): Boolean = name == Thy_Header.PURE

  def illegal_session(name: String): Boolean = name == "" || name == DRAFT
  def illegal_theory(name: String): Boolean =
    name == root_name || File_Format.registry.theory_excluded(name)


  /* ROOTS file format */

  class ROOTS_File_Format extends File_Format {
    val format_name: String = roots_name
    val file_ext = ""

    override def detect(name: String): Boolean =
      Url.get_base_name(name) match {
        case Some(base_name) => base_name == roots_name
        case None => false
      }

    override def theory_suffix: String = "ROOTS_file"
    override def theory_content(name: String): String =
      """theory "ROOTS" imports Pure begin ROOTS_file "." end"""
    override def theory_excluded(name: String): Boolean = name == "ROOTS"
  }


  /* base info */

  object Base {
    val bootstrap: Base = Base(overall_syntax = Thy_Header.bootstrap_syntax)
  }

  sealed case class Base(
    session_name: String = "",
    session_pos: Position.T = Position.none,
    proper_session_theories: List[Document.Node.Name] = Nil,
    document_theories: List[Document.Node.Name] = Nil,
    loaded_theories: Graph[String, Outer_Syntax] = Graph.string,  // cumulative imports
    used_theories: List[(Document.Node.Name, Options)] = Nil,  // new imports
    theory_load_commands: Map[String, List[Command_Span.Span]] = Map.empty,
    known_theories: Map[String, Document.Node.Entry] = Map.empty,
    known_loaded_files: Map[String, List[Path]] = Map.empty,
    overall_syntax: Outer_Syntax = Outer_Syntax.empty,
    imported_sources: List[(Path, SHA1.Digest)] = Nil,
    session_sources: List[(Path, SHA1.Digest)] = Nil,
    session_graph_display: Graph_Display.Graph = Graph_Display.empty_graph,
    errors: List[String] = Nil
  ) {
    def session_entry: (String, Base) = session_name -> this

    override def toString: String = "Sessions.Base(" + print_body + ")"
    def print_body: String =
      "session_name = " + quote(session_name) +
      ", loaded_theories = " + loaded_theories.size +
      ", used_theories = " + used_theories.length

    def all_sources: List[(Path, SHA1.Digest)] = imported_sources ::: session_sources

    def all_document_theories: List[Document.Node.Name] =
      proper_session_theories ::: document_theories

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


  /* background context */

  object Background {
    def empty(session: String): Background =
      Background(Base(session_name = session))

    def load(options: Options,
      session: String,
      progress: Progress = new Progress,
      dirs: List[Path] = Nil,
      include_sessions: List[String] = Nil,
      session_ancestor: Option[String] = None,
      session_requirements: Boolean = false
    ): Background = {
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
              if !ancestor_loaded(thy) && selected_sessions.theory_qualifier(thy) != session
            }
            yield thy

          if (required_theories.isEmpty) (ancestor.get, Nil)
          else {
            val other_name = info.name + "_requirements(" + ancestor.get + ")"
            Isabelle_System.isabelle_tmp_prefix()

            (other_name,
              List(
                Info.make(
                  Chapter_Defs.empty,
                  Options.init0(),
                  info.options,
                  augment_options = _ => Nil,
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
                    export_files = Nil,
                    export_classpath = Nil))))
          }
        }
        else (session, Nil)

      val full_sessions1 =
        if (infos1.isEmpty) full_sessions
        else load_structure(options, dirs = dirs, infos = infos1)

      val selected_sessions1 =
        full_sessions1.selection(Selection(sessions = session1 :: session :: include_sessions))

      val deps1 = Sessions.deps(selected_sessions1, progress = progress)

      Background(deps1(session1), sessions_structure = full_sessions1,
        errors = deps1.errors, infos = infos1)
    }
  }

  sealed case class Background(
    base: Base,
    sessions_structure: Structure = Structure.empty,
    errors: List[String] = Nil,
    infos: List[Info] = Nil
  ) {
    def session_name: String = base.session_name
    def info: Info = sessions_structure(session_name)

    def check_errors: Background =
      if (errors.isEmpty) this
      else error(cat_lines(errors))
  }


  /* source dependencies */

  object Deps {
    def load(sessions_structure: Structure,
      progress: Progress = new Progress,
      inlined_files: Boolean = false,
      list_files: Boolean = false
    ): Deps = {
      var cache_sources = Map.empty[JFile, SHA1.Digest]
      def check_sources(paths: List[Path]): List[(Path, SHA1.Digest)] = {
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
        sessions_structure.imports_topological_order.foldLeft(Map(Base.bootstrap.session_entry)) {
          case (session_bases, session_name) =>
            progress.expose_interrupt()

            val info = sessions_structure(session_name)
            try {
              val deps_base = info.deps_base(session_bases)
              val session_background =
                Background(base = deps_base, sessions_structure = sessions_structure)
              val resources = new Resources(session_background)

              progress.echo(
                "Session " + info.chapter + "/" + session_name +
                  if_proper(info.groups, info.groups.mkString(" (", " ", ")")),
                verbose = !list_files)

              val dependencies = resources.session_dependencies(info)

              val proper_session_theories =
                dependencies.theories.filter(name =>
                  sessions_structure.theory_qualifier(name) == session_name)

              val theory_files = dependencies.theories.map(_.path)

              val (load_commands, load_commands_errors) =
                try { if (inlined_files) (dependencies.load_commands, Nil) else (Nil, Nil) }
                catch { case ERROR(msg) => (Nil, List(msg)) }

              val theory_load_commands =
                (for ((name, span) <- load_commands.iterator) yield name.theory -> span).toMap

              val loaded_files: List[(String, List[Path])] =
                for ((name, spans) <- load_commands) yield {
                  val (theory, files) = dependencies.loaded_files(name, spans)
                  theory -> files.map(file => Path.explode(file.node))
                }

              val document_files =
                for ((path1, path2) <- info.document_files)
                  yield info.dir + path1 + path2

              val session_files =
                (theory_files ::: loaded_files.flatMap(_._2) ::: document_files).map(_.expand)

              val imported_files = if (inlined_files) dependencies.imported_files else Nil

              if (list_files) {
                progress.echo(cat_lines(session_files.map(_.implode).sorted.map("  " + _)))
              }

              val session_graph_display: Graph_Display.Graph = {
                def session_node(name: String): Graph_Display.Node =
                  Graph_Display.Node("[" + name + "]", "session." + name)

                def node(name: Document.Node.Name): Graph_Display.Node = {
                  val qualifier = sessions_structure.theory_qualifier(name)
                  if (qualifier == info.name) {
                    Graph_Display.Node(name.theory_base_name, "theory." + name.theory)
                  }
                  else session_node(qualifier)
                }

                val required_sessions =
                  dependencies.loaded_theories.all_preds(dependencies.theories.map(_.theory))
                    .map(theory => sessions_structure.theory_qualifier(theory))
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

              val import_errors = {
                val known_sessions =
                  sessions_structure.imports_requirements(List(session_name)).toSet
                for {
                  name <- dependencies.theories
                  qualifier = sessions_structure.theory_qualifier(name)
                  if !known_sessions(qualifier)
                } yield "Bad import of theory " + quote(name.toString) +
                  ": need to include sessions " + quote(qualifier) + " in ROOT"
              }

              val document_errors =
                info.document_theories.flatMap(
                {
                  case (thy, pos) =>
                    val build_hierarchy =
                      if (sessions_structure.build_graph.defined(session_name)) {
                        sessions_structure.build_hierarchy(session_name)
                      }
                      else Nil

                    def err(msg: String): Option[String] =
                      Some(msg + " " + quote(thy) + Position.here(pos))

                    known_theories.get(thy).map(_.name) match {
                      case None => err("Unknown document theory")
                      case Some(name) =>
                        val qualifier = sessions_structure.theory_qualifier(name)
                        if (proper_session_theories.contains(name)) {
                          err("Redundant document theory from this session:")
                        }
                        else if (
                          !build_hierarchy.contains(qualifier) &&
                          !dependencies.theories.contains(name)
                        ) {
                          err("Document theory from other session not imported properly:")
                        }
                        else None
                    }
                })
              val document_theories =
                info.document_theories.map({ case (thy, _) => known_theories(thy).name })

              val dir_errors = {
                val ok = info.dirs.map(_.canonical_file).toSet
                val bad =
                  (for {
                    name <- proper_session_theories.iterator
                    path = Path.explode(name.master_dir)
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
                    name <- proper_session_theories.iterator
                    name1 <- resources.find_theory_node(name.theory)
                    if name.node != name1.node
                  } yield {
                    "Incoherent theory file import:\n  " + quote(name.node) +
                      " vs. \n  " + quote(name1.node)
                  }).toList

                errs1 ::: errs2 ::: errs3 ::: errs4
              }

              val sources_errors =
                for (p <- session_files if !p.is_file) yield "No such file: " + p

              val path_errors =
                try { Path.check_case_insensitive(session_files ::: imported_files); Nil }
                catch { case ERROR(msg) => List(msg) }

              val bibtex_errors = info.bibtex_entries.errors

              val base =
                Base(
                  session_name = info.name,
                  session_pos = info.pos,
                  proper_session_theories = proper_session_theories,
                  document_theories = document_theories,
                  loaded_theories = dependencies.loaded_theories,
                  used_theories = dependencies.theories_adjunct,
                  theory_load_commands = theory_load_commands,
                  known_theories = known_theories,
                  known_loaded_files = known_loaded_files,
                  overall_syntax = dependencies.overall_syntax,
                  imported_sources = check_sources(imported_files),
                  session_sources = check_sources(session_files),
                  session_graph_display = session_graph_display,
                  errors = dependencies.errors ::: load_commands_errors ::: import_errors :::
                    document_errors ::: dir_errors ::: sources_errors ::: path_errors :::
                    bibtex_errors)

              session_bases + base.session_entry
            }
            catch {
              case ERROR(msg) =>
                cat_error(msg, "The error(s) above occurred in session " +
                  quote(info.name) + Position.here(info.pos))
            }
        }

      new Deps(sessions_structure, session_bases)
    }
  }

  final class Deps private[Sessions](
    val sessions_structure: Structure,
    val session_bases: Map[String, Base]
  ) {
    def background(session: String): Background =
      Background(base = apply(session), sessions_structure = sessions_structure, errors = errors)

    def is_empty: Boolean = session_bases.keysIterator.forall(_.isEmpty)
    def apply(name: String): Base = session_bases(name)
    def get(name: String): Option[Base] = session_bases.get(name)

    def sources_shasum(name: String): SHA1.Shasum = {
      val meta_info = sessions_structure(name).meta_info
      val sources =
        SHA1.shasum_sorted(
          for ((path, digest) <- apply(name).all_sources)
            yield digest -> File.symbolic_path(path))
      meta_info ::: sources
    }

    def errors: List[String] =
      (for {
        (name, base) <- session_bases.iterator
        if base.errors.nonEmpty
      } yield cat_lines(base.errors) +
          "\nThe error(s) above occurred in session " + quote(name) + Position.here(base.session_pos)
      ).toList

    def check_errors: Deps =
      errors match {
        case Nil => this
        case errs => error(cat_lines(errs))
      }

    override def toString: String = "Sessions.Deps(" + sessions_structure + ")"
  }


  /* notable groups */

  sealed case class Group_Info(
    name: String,
    description: String,
    bulky: Boolean = false,
    afp: Boolean = false
  ) {
    override def toString: String = name
  }

  lazy val notable_groups: List[Group_Info] =
    List(
      Group_Info("large", "full 64-bit memory model or word arithmetic required",
        bulky = true, afp = true),
      Group_Info("slow", "CPU time much higher than 60min (on mid-range hardware)",
        bulky = true, afp = true),
      Group_Info("very_slow", "elapsed time of many hours (on high-end hardware)",
        bulky = true, afp = true),
      Group_Info("AFP", "entry within AFP", afp = true),
      Group_Info("doc", "Isabelle documentation"),
      Group_Info("no_doc", "suppressed Isabelle documentation")
    )

  lazy val bulky_groups: Set[String] =
    Set.from(notable_groups.flatMap(g => if (g.bulky) Some(g.name) else None))

  lazy val afp_groups: Set[String] =
    Set.from(notable_groups.flatMap(g => if (g.afp) Some(g.name) else None))


  /* cumulative session info */

  private val BUILD_PREFS_BG = "<build_prefs:"
  private val BUILD_PREFS_EN = ">"

  def make_build_prefs(name: String): String =
    BUILD_PREFS_BG + name + BUILD_PREFS_EN

  def is_build_prefs(s: String): Boolean = {
    val i = s.indexOf('<')
    i >= 0 && {
      val s1 = s.substring(i)
      s1.startsWith(BUILD_PREFS_BG) && s1.endsWith(BUILD_PREFS_EN)
    }
  }

  def eq_sources(thorough: Boolean, shasum1: SHA1.Shasum, shasum2: SHA1.Shasum): Boolean =
    if (thorough) shasum1 == shasum2
    else {
      def trim(shasum: SHA1.Shasum): SHA1.Shasum =
        shasum.filter(s => !is_build_prefs(s))

      trim(shasum1) == trim(shasum2)
    }

  sealed case class Chapter_Info(
    name: String,
    pos: Position.T,
    groups: List[String],
    description: String,
    sessions: List[String]
  )

  object Info {
    def make(
      chapter_defs: Chapter_Defs,
      options0: Options,
      options: Options,
      augment_options: String => List[Options.Spec],
      dir_selected: Boolean,
      dir: Path,
      chapter: String,
      entry: Session_Entry
    ): Info = {
      try {
        val name = entry.name

        if (illegal_session(name)) error("Illegal session name " + quote(name))
        if (is_pure(name) && entry.parent.isDefined) error("Illegal parent session")
        if (!is_pure(name) && !entry.parent.isDefined) error("Missing parent session")

        val session_path = dir + Path.explode(entry.path)
        val directories = entry.directories.map(dir => session_path + Path.explode(dir))

        val session_options0 = options ++ entry.options
        val session_options = session_options0 ++ augment_options(name)
        val session_prefs =
          session_options.make_prefs(defaults = session_options0, filter = _.session_content)

        val build_prefs_digests =
          session_options.changed(defaults = options0, filter = _.session_content)
            .map(ch => SHA1.digest(ch.print_prefs) -> make_build_prefs(ch.name))

        val theories =
          entry.theories.map({ case (opts, thys) =>
            (session_options ++ opts,
              thys.map({ case ((thy, pos), _) =>
                val thy_name = Thy_Header.import_name(thy)
                if (illegal_theory(thy_name)) {
                  error("Illegal theory name " + quote(thy_name) + Position.here(pos))
                }
                else (thy, pos) })) })

        val global_theories =
          for { (_, thys) <- entry.theories; ((thy, pos), global) <- thys if global }
          yield {
            val thy_name = Path.explode(thy).file_name
            if (Long_Name.is_qualified(thy_name)) {
              error("Bad qualified name for global theory " +
                quote(thy_name) + Position.here(pos))
            }
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
              entry.theories_no_position, conditions, entry.document_theories_no_position).toString)

        val meta_info =
          SHA1.shasum_meta_info(meta_digest) ::: SHA1.shasum_sorted(build_prefs_digests)

        val chapter_groups = chapter_defs(chapter).groups
        val groups = chapter_groups ::: entry.groups.filterNot(chapter_groups.contains)

        Info(name, chapter, dir_selected, entry.pos, groups, session_path,
          entry.parent, entry.description, directories, session_options, session_prefs,
          entry.imports, theories, global_theories, entry.document_theories, document_files,
          export_files, entry.export_classpath, meta_info)
      }
      catch {
        case ERROR(msg) =>
          error(msg + "\nThe error(s) above occurred in session entry " +
            quote(entry.name) + Position.here(entry.pos))
      }
    }
  }

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
    session_prefs: String,
    imports: List[String],
    theories: List[(Options, List[(String, Position.T)])],
    global_theories: List[String],
    document_theories: List[(String, Position.T)],
    document_files: List[(Path, Path)],
    export_files: List[(Path, Int, List[String])],
    export_classpath: List[String],
    meta_info: SHA1.Shasum
  ) {
    def deps: List[String] = parent.toList ::: imports

    def deps_base(session_bases: String => Base): Base = {
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

    def main_group: Boolean = groups.contains("main")
    def doc_group: Boolean = groups.contains("doc")

    def build_thorough: Boolean = options.bool("build_thorough")

    def timeout_ignored: Boolean =
      !options.bool("timeout_build") || Time.seconds(options.real("timeout")) < Time.ms(1)

    def timeout: Time = Time.seconds(options.real("timeout") * options.real("timeout_scale"))

    def document_enabled: Boolean =
      options.string("document") match {
        case "" | "false" => false
        case "pdf" | "true" => true
        case doc => error("Bad document specification " + quote(doc))
      }

    def document_variants: List[Document_Build.Document_Variant] = {
      val variants =
        space_explode(':', options.string("document_variants")).
          map(Document_Build.Document_Variant.parse)

      val dups = Library.duplicates(variants.map(_.name))
      if (dups.nonEmpty) error("Duplicate document variants: " + commas_quote(dups))

      variants
    }

    def document_echo: Boolean = options.bool("document_echo")

    def documents: List[Document_Build.Document_Variant] = {
      val variants = document_variants
      if (!document_enabled || document_files.isEmpty) Nil else variants
    }

    def document_output: Option[Path] =
      options.string("document_output") match {
        case "" => None
        case s => Some(dir + Path.explode(s))
      }

    def browser_info: Boolean = options.bool("browser_info")

    lazy val bibtex_entries: Bibtex.Entries =
      (for {
        (document_dir, file) <- document_files.iterator
        if File.is_bib(file.file_name)
      } yield {
        val path = dir + document_dir + file
        Bibtex.Entries.parse(File.read(path), start = Token.Pos.file(File.standard_path(path)))
      }).foldRight(Bibtex.Entries.empty)(_ ::: _)

    def record_proofs: Boolean = options.int("record_proofs") >= 2

    def is_afp: Boolean = chapter == AFP.chapter
    def is_afp_bulky: Boolean = is_afp && groups.exists(bulky_groups)
  }

  object Selection {
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
    sessions: List[String] = Nil
  ) {
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

  object Structure {
    val empty: Structure = make(Options.empty)

    def make(
      options: Options,
      augment_options: String => List[Options.Spec] = _ => Nil,
      roots: List[Root_File] = Nil,
      infos: List[Info] = Nil
    ): Structure = {
      val chapter_defs: Chapter_Defs =
        roots.foldLeft(Chapter_Defs.empty) {
          case (defs1, root) =>
            root.entries.foldLeft(defs1) {
              case (defs2, entry: Chapter_Def) => defs2 + entry
              case (defs2, _) => defs2
            }
        }

      val options0 = Options.init0()
      val session_prefs = options.make_prefs(defaults = options0, filter = _.session_content)

      val root_infos = {
        var chapter = UNSORTED
        val root_infos = new mutable.ListBuffer[Info]
        for (root <- roots) {
          root.entries.foreach {
            case entry: Chapter_Entry => chapter = entry.name
            case entry: Session_Entry =>
              root_infos +=
                Info.make(chapter_defs, options0, options, augment_options,
                  root.select, root.dir, chapter, entry)
            case _ =>
          }
          chapter = UNSORTED
        }
        root_infos.toList
      }

      val info_graph =
        (root_infos ::: infos).foldLeft(Graph.string[Info]) {
          case (graph, info) =>
            if (graph.defined(info.name)) {
              error("Duplicate session " + quote(info.name) + Position.here(info.pos) +
                Position.here(graph.get_node(info.name).pos))
            }
            else graph.new_node(info.name, info)
        }

      def augment_graph(
        graph: Graph[String, Info],
        kind: String,
        edges: Info => Iterable[String]
      ) : Graph[String, Info] = {
        def add_edge(pos: Position.T, name: String, g: Graph[String, Info], parent: String) = {
          if (!g.defined(parent)) {
            error("Bad " + kind + " session " + quote(parent) + " for " +
              quote(name) + Position.here(pos))
          }

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

      val build_graph = augment_graph(info_graph, "parent", _.parent)
      val imports_graph = augment_graph(build_graph, "imports", _.imports)

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
          yield (info, thy)
        ).foldLeft(Thy_Header.bootstrap_global_theories.toMap) {
            case (global, (info, thy)) =>
              val qualifier = info.name
              global.get(thy) match {
                case Some(qualifier1) if qualifier != qualifier1 =>
                  error("Duplicate global theory " + quote(thy) + Position.here(info.pos))
                case _ => global + (thy -> qualifier)
              }
          }

      new Structure(chapter_defs, session_prefs, session_positions, session_directories,
        global_theories, build_graph, imports_graph)
    }
  }

  final class Structure private[Sessions](
    chapter_defs: Chapter_Defs,
    val session_prefs: String,
    val session_positions: List[(String, Position.T)],
    val session_directories: Map[JFile, String],
    val global_theories: Map[String, String],
    val build_graph: Graph[String, Info],
    val imports_graph: Graph[String, Info]
  ) {
    sessions_structure =>

    def dest_session_directories: List[(String, String)] =
      for ((file, session) <- session_directories.toList)
        yield (File.standard_path(file), session)

    lazy val known_chapters: List[Chapter_Info] = {
      val chapter_sessions =
        Multi_Map.from(
          for ((_, (info, _)) <- build_graph.iterator)
            yield info.chapter -> info.name)
      val chapters1 =
        (for (entry <- chapter_defs.list.iterator) yield {
          val sessions = chapter_sessions.get_list(entry.name)
          Chapter_Info(entry.name, entry.pos, entry.groups, entry.description, sessions.sorted)
        }).toList
      val chapters2 =
        (for {
          (name, sessions) <- chapter_sessions.iterator_list
          if !chapters1.exists(_.name == name)
        } yield Chapter_Info(name, Position.none, Nil, "", sessions.sorted)).toList.sortBy(_.name)
      chapters1 ::: chapters2
    }

    def relevant_chapters: List[Chapter_Info] = known_chapters.filter(_.sessions.nonEmpty)

    def build_graph_display: Graph_Display.Graph = Graph_Display.make_graph(build_graph)
    def imports_graph_display: Graph_Display.Graph = Graph_Display.make_graph(imports_graph)

    def defined(name: String): Boolean = imports_graph.defined(name)
    def apply(name: String): Info = imports_graph.get_node(name)
    def get(name: String): Option[Info] = if (defined(name)) Some(apply(name)) else None

    def theory_qualifier(name: String): String =
      global_theories.getOrElse(name, Long_Name.qualifier(name))
    def theory_qualifier(name: Document.Node.Name): String = theory_qualifier(name.theory)

    def check_sessions(names: List[String]): Unit = {
      val bad_sessions = SortedSet(names.filterNot(defined): _*).toList
      if (bad_sessions.nonEmpty) {
        error("Undefined session(s): " + commas_quote(bad_sessions))
      }
    }

    def check_sessions(sel: Selection): Unit =
      check_sessions(sel.base_sessions ::: sel.exclude_sessions ::: sel.sessions)

    private def selected(graph: Graph[String, Info], sel: Selection): List[String] = {
      check_sessions(sel)

      val select_group = sel.session_groups.toSet
      val select_session = sel.sessions.toSet ++ imports_graph.all_succs(sel.base_sessions)

      val selected0 =
        if (sel.all_sessions) graph.keys
        else {
          (for {
            (name, (info, _)) <- graph.iterator
            if info.dir_selected || select_session(name) || info.groups.exists(select_group)
          } yield name).toList
        }

      if (sel.requirements) (graph.all_preds(selected0).toSet -- selected0).toList
      else selected0
    }

    def selection(sel: Selection): Structure = {
      check_sessions(sel)

      val excluded = {
        val exclude_group = sel.exclude_session_groups.toSet
        val exclude_group_sessions =
          (for {
            (name, (info, _)) <- imports_graph.iterator
            if info.groups.exists(exclude_group)
          } yield name).toList
        imports_graph.all_succs(exclude_group_sessions ::: sel.exclude_sessions).toSet
      }

      def restrict(graph: Graph[String, Info]): Graph[String, Info] = {
        val sessions = graph.all_preds(selected(graph, sel)).filterNot(excluded)
        graph.restrict(graph.all_preds(sessions).toSet)
      }

      new Structure(chapter_defs, session_prefs, session_positions, session_directories,
        global_theories, restrict(build_graph), restrict(imports_graph))
    }

    def selection(session: String): Structure = selection(Selection.session(session))

    def selection_deps(
      selection: Selection,
      progress: Progress = new Progress,
      loading_sessions: Boolean = false,
      inlined_files: Boolean = false
    ): Deps = {
      val deps =
        Sessions.deps(sessions_structure.selection(selection),
          progress = progress, inlined_files = inlined_files)

      if (loading_sessions) {
        val selection_size = deps.sessions_structure.build_graph.size
        if (selection_size > 1) progress.echo("Loading " + selection_size + " sessions ...")
      }

      deps
    }

    def build_hierarchy(session: String): List[String] =
      if (build_graph.defined(session)) build_graph.all_preds(List(session))
      else List(session)

    def build_selection(sel: Selection): List[String] = selected(build_graph, sel)
    def build_descendants(ss: List[String]): List[String] = build_graph.all_succs(ss)
    def build_requirements(ss: List[String]): List[String] = build_graph.all_preds_rev(ss)
    def build_topological_order: List[String] = build_graph.topological_order

    def imports_selection(sel: Selection): List[String] = selected(imports_graph, sel)
    def imports_descendants(ss: List[String]): List[String] = imports_graph.all_succs(ss)
    def imports_requirements(ss: List[String]): List[String] = imports_graph.all_preds_rev(ss)
    def imports_topological_order: List[String] = imports_graph.topological_order

    override def toString: String =
      imports_graph.keys_iterator.mkString("Sessions.Structure(", ", ", ")")
  }


  /* parser */

  private val CHAPTER_DEFINITION = "chapter_definition"
  private val CHAPTER = "chapter"
  private val SESSION = "session"
  private val DESCRIPTION = "description"
  private val DIRECTORIES = "directories"
  private val OPTIONS = "options"
  private val SESSIONS = "sessions"
  private val THEORIES = "theories"
  private val GLOBAL = "global"
  private val DOCUMENT_THEORIES = "document_theories"
  private val DOCUMENT_FILES = "document_files"
  private val EXPORT_FILES = "export_files"
  private val EXPORT_CLASSPATH = "export_classpath"

  val root_syntax: Outer_Syntax =
    Outer_Syntax.empty + "(" + ")" + "+" + "," + "=" + "[" + "]" + "in" +
      GLOBAL +
      (CHAPTER_DEFINITION, Keyword.THY_DECL) +
      (CHAPTER, Keyword.THY_DECL) +
      (SESSION, Keyword.THY_DECL) +
      (DESCRIPTION, Keyword.QUASI_COMMAND) +
      (DIRECTORIES, Keyword.QUASI_COMMAND) +
      (OPTIONS, Keyword.QUASI_COMMAND) +
      (SESSIONS, Keyword.QUASI_COMMAND) +
      (THEORIES, Keyword.QUASI_COMMAND) +
      (DOCUMENT_THEORIES, Keyword.QUASI_COMMAND) +
      (DOCUMENT_FILES, Keyword.QUASI_COMMAND) +
      (EXPORT_FILES, Keyword.QUASI_COMMAND) +
      (EXPORT_CLASSPATH, Keyword.QUASI_COMMAND)

  abstract class Entry
  object Chapter_Def {
    def empty(chapter: String): Chapter_Def = Chapter_Def(Position.none, chapter, Nil, "")
  }
  sealed case class Chapter_Def(
    pos: Position.T,
    name: String,
    groups: List[String],
    description: String
  ) extends Entry
  sealed case class Chapter_Entry(name: String) extends Entry
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
    export_files: List[(String, Int, List[String])],
    export_classpath: List[String]
  ) extends Entry {
    def theories_no_position: List[(List[Options.Spec], List[(String, Boolean)])] =
      theories.map({ case (a, b) => (a, b.map({ case ((c, _), d) => (c, d) })) })
    def document_theories_no_position: List[String] =
      document_theories.map(_._1)
  }

  object Chapter_Defs {
    val empty: Chapter_Defs = new Chapter_Defs(Nil)
  }

  class Chapter_Defs private(rev_list: List[Chapter_Def]) {
    def list: List[Chapter_Def] = rev_list.reverse

    override def toString: String =
      list.map(_.name).mkString("Chapter_Defs(", ", ", ")")

    def get(chapter: String): Option[Chapter_Def] =
      rev_list.find(_.name == chapter)

    def apply(chapter: String): Chapter_Def =
      get(chapter) getOrElse Chapter_Def.empty(chapter)

    def + (entry: Chapter_Def): Chapter_Defs =
      get(entry.name) match {
        case None => new Chapter_Defs(entry :: rev_list)
        case Some(old_entry) =>
          error("Duplicate chapter definition " + quote(entry.name) +
            Position.here(old_entry.pos) + Position.here(entry.pos))
      }
  }

  private object Parsers extends Options.Parsers {
    private val groups: Parser[List[String]] =
      ($$$("(") ~! (rep1(name) <~ $$$(")")) ^^ { case _ ~ x => x }) | success(Nil)

    private val description: Parser[String] =
      ($$$(DESCRIPTION) ~! text ^^ { case _ ~ x => x }) | success("")

    private val chapter_def: Parser[Chapter_Def] =
      command(CHAPTER_DEFINITION) ~! (position(chapter_name) ~ groups ~ description) ^^
        { case _ ~ ((a, pos) ~ b ~ c) => Chapter_Def(pos, a, b, c) }

    private val chapter_entry: Parser[Chapter_Entry] =
      command(CHAPTER) ~! chapter_name ^^ { case _ ~ a => Chapter_Entry(a) }

    private val session_entry: Parser[Session_Entry] = {
      val options = $$$("[") ~> rep1sep(option_spec, $$$(",")) <~ $$$("]")

      val theory_entry =
        position(theory_name) ~ opt_keyword(GLOBAL) ^^ { case x ~ y => (x, y) }

      val theories =
        $$$(THEORIES) ~!
          ((options | success(Nil)) ~ rep1(theory_entry)) ^^
          { case _ ~ (x ~ y) => (x, y) }

      val document_theories =
        $$$(DOCUMENT_THEORIES) ~! rep1(position(name)) ^^ { case _ ~ x => x }

      val document_files =
        $$$(DOCUMENT_FILES) ~! (in_path_parens("document") ~ rep1(path)) ^^
          { case _ ~ (x ~ y) => y.map((x, _)) }

      val prune = $$$("[") ~! (nat ~ $$$("]")) ^^ { case _ ~ (x ~ _) => x } | success(0)

      val export_files =
        $$$(EXPORT_FILES) ~! (in_path_parens("export") ~ prune ~ rep1(embedded)) ^^
          { case _ ~ (x ~ y ~ z) => (x, y, z) }

      val export_classpath =
        $$$(EXPORT_CLASSPATH) ~! (rep1(embedded) | success(List("*:classpath/*.jar"))) ^^
          { case _ ~ x => x }

      command(SESSION) ~!
        (position(session_name) ~ groups ~ in_path(".") ~
          ($$$("=") ~!
            (opt(session_name ~! $$$("+") ^^ { case x ~ _ => x }) ~ description ~
              (($$$(OPTIONS) ~! options ^^ { case _ ~ x => x }) | success(Nil)) ~
              (($$$(SESSIONS) ~! rep1(session_name)  ^^ { case _ ~ x => x }) | success(Nil)) ~
              (($$$(DIRECTORIES) ~! rep1(path) ^^ { case _ ~ x => x }) | success(Nil)) ~
              rep(theories) ~
              (opt(document_theories) ^^ (x => x.getOrElse(Nil))) ~
              (rep(document_files) ^^ (x => x.flatten)) ~
              rep(export_files) ~
              opt(export_classpath)))) ^^
        { case _ ~ ((a, pos) ~ b ~ c ~ (_ ~ (d ~ e ~ f ~ g ~ h ~ i ~ j ~ k ~ l ~ m))) =>
            Session_Entry(pos, a, b, c, d, e, f, g, h, i, j, k, l, m.getOrElse(Nil)) }
    }

    def parse_root(path: Path): List[Entry] = {
      val toks = Token.explode(root_syntax.keywords, File.read(path))
      val start = Token.Pos.file(path.implode)
      val parser: Parser[Entry] = chapter_def | chapter_entry | session_entry
      parse_all(rep(parser), Token.reader(toks, start)) match {
        case Success(result, _) => result
        case bad => error(bad.toString)
      }
    }
  }

  def parse_root(path: Path): List[Entry] = Parsers.parse_root(path)

  def parse_root_entries(path: Path): List[Session_Entry] =
    Parsers.parse_root(path).flatMap(Library.as_subclass(classOf[Session_Entry]))

  def parse_roots(roots: Path): List[String] = {
    for {
      line <- split_lines(File.read(roots))
      if !(line == "" || line.startsWith("#"))
    } yield line
  }


  /* load sessions from certain directories */

  def is_session_dir(dir: Path, ssh: SSH.System = SSH.Local): Boolean =
    ssh.is_file(dir + ROOT) || ssh.is_file(dir + ROOTS)

  def check_session_dir(dir: Path): Path =
    if (is_session_dir(dir)) dir.absolute
    else {
      error("Bad session root directory: " + dir.expand.toString +
        "\n  (missing \"ROOT\" or \"ROOTS\")")
    }

  def directories(dirs: List[Path], select_dirs: List[Path]): List[(Boolean, Path)] = {
    val default_dirs = Components.directories().filter(is_session_dir(_))
    for { (select, dir) <- (default_dirs ::: dirs).map((false, _)) ::: select_dirs.map((true, _)) }
    yield (select, dir.canonical)
  }

  sealed case class Root_File(path: Path, select: Boolean) {
    val key: JFile = path.canonical_file
    def dir: Path = path.dir

    lazy val entries: List[Entry] = Parsers.parse_root(path)
  }

  def load_root_files(
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil
  ): List[Root_File] = {
    def load_dir(select: Boolean, dir: Path): List[Root_File] =
      load_root(select, dir) ::: load_roots(select, dir)

    def load_root(select: Boolean, dir: Path): List[Root_File] = {
      val root = dir + ROOT
      if (root.is_file) List(Root_File(root, select)) else Nil
    }

    def load_roots(select: Boolean, dir: Path): List[Root_File] = {
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

    val raw_roots: List[Root_File] =
      for {
        (select, dir) <- directories(dirs, select_dirs)
        root <- load_dir(select, check_session_dir(dir))
      } yield root

    var next_root = 0
    var seen_roots = Map.empty[JFile, (Root_File, Int)]
    for (root <- raw_roots) {
      seen_roots.get(root.key) match {
        case None =>
          seen_roots += (root.key -> (root, next_root))
          next_root += 1
        case Some((root0, next0)) =>
          val root1 = root0.copy(select = root0.select || root.select)
          seen_roots += (root0.key -> (root1, next0))
      }
    }
    seen_roots.valuesIterator.toList.sortBy(_._2).map(_._1)
  }


  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("sessions", "explore structure of Isabelle sessions",
    Scala_Project.here,
    { args =>
      var base_sessions: List[String] = Nil
      var select_dirs: List[Path] = Nil
      var requirements = false
      var exclude_session_groups: List[String] = Nil
      var all_sessions = false
      var build_graph = false
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
    -b           follow session build dependencies (default: source imports)
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
        "b" -> (_ => build_graph = true),
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

      val order =
        if (build_graph) sessions_structure.build_topological_order
        else sessions_structure.imports_topological_order
      for (name <- order) Output.writeln(name, stdout = true)
    })
}
