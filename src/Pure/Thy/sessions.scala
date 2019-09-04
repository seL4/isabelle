/*  Title:      Pure/Thy/sessions.scala
    Author:     Makarius

Cumulative session information.
*/

package isabelle

import java.io.{File => JFile}
import java.nio.ByteBuffer
import java.nio.channels.FileChannel
import java.nio.file.StandardOpenOption

import scala.collection.{SortedSet, SortedMap}
import scala.collection.mutable


object Sessions
{
  /* session and theory names */

  val root_name: String = "ROOT"
  val theory_name: String = "Pure.Sessions"

  val UNSORTED = "Unsorted"
  val DRAFT = "Draft"

  def is_pure(name: String): Boolean = name == Thy_Header.PURE


  def exclude_session(name: String): Boolean = name == "" || name == DRAFT

  def exclude_theory(name: String): Boolean =
    name == root_name || name == "README" || name == "index" || name == "bib"


  /* base info and source dependencies */

  object Known
  {
    val empty: Known = Known()

    def make(local_dir: Path, bases: List[Base],
      sessions: List[(String, Position.T)] = Nil,
      theories: List[Document.Node.Entry] = Nil,
      loaded_files: List[(String, List[Path])] = Nil): Known =
    {
      def bases_iterator(local: Boolean) =
        for {
          base <- bases.iterator
          (_, entry) <- (if (local) base.known.theories_local else base.known.theories).iterator
        } yield entry

      def local_theories_iterator =
      {
        val local_path = local_dir.canonical_file.toPath
        theories.iterator.filter(entry =>
          entry.name.path.canonical_file.toPath.startsWith(local_path))
      }

      val known_sessions =
        (sessions.toMap /: bases)({ case (known, base) => known ++ base.known.sessions })

      val known_theories =
        (Map.empty[String, Document.Node.Entry] /: (bases_iterator(false) ++ theories.iterator))({
          case (known, entry) =>
            known.get(entry.name.theory) match {
              case Some(entry1) if entry.name != entry1.name =>
                error("Duplicate theory " + quote(entry.name.node) + " vs. " +
                  quote(entry1.name.node))
              case _ => known + (entry.name.theory -> entry)
            }
          })
      val known_theories_local =
        (Map.empty[String, Document.Node.Entry] /:
            (bases_iterator(true) ++ local_theories_iterator))({
          case (known, entry) => known + (entry.name.theory -> entry)
        })
      val known_files =
        (Map.empty[JFile, List[Document.Node.Name]] /:
            (bases_iterator(true) ++ bases_iterator(false) ++ theories.iterator))({
          case (known, entry) =>
            val name = entry.name
            val file = name.path.canonical_file
            val theories1 = known.getOrElse(file, Nil)
            if (theories1.exists(name1 => name.node == name1.node && name.theory == name1.theory))
              known
            else known + (file -> (name :: theories1))
        })

      val known_loaded_files =
        (loaded_files.toMap /: bases.map(base => base.known.loaded_files))(_ ++ _)

      Known(
        known_sessions,
        known_theories,
        known_theories_local,
        known_files.iterator.map(p => (p._1, p._2.reverse)).toMap,
        known_loaded_files)
    }
  }

  sealed case class Known(
    sessions: Map[String, Position.T] = Map.empty,
    theories: Map[String, Document.Node.Entry] = Map.empty,
    theories_local: Map[String, Document.Node.Entry] = Map.empty,
    files: Map[JFile, List[Document.Node.Name]] = Map.empty,
    loaded_files: Map[String, List[Path]] = Map.empty)
  {
    def platform_path: Known =
      copy(theories = for ((a, b) <- theories) yield (a, b.map(File.platform_path(_))),
        theories_local = for ((a, b) <- theories_local) yield (a, b.map(File.platform_path(_))),
        files = for ((a, b) <- files) yield (a, b.map(c => c.map(File.platform_path(_)))))

    def standard_path: Known =
      copy(theories = for ((a, b) <- theories) yield (a, b.map(File.standard_path(_))),
        theories_local = for ((a, b) <- theories_local) yield (a, b.map(File.standard_path(_))),
        files = for ((a, b) <- files) yield (a, b.map(c => c.map(File.standard_path(_)))))

    def theory_names: List[Document.Node.Name] = theories.iterator.map(p => p._2.name).toList

    lazy val theory_graph: Document.Theory_Graph[Unit] =
      Document.theory_graph(
        for ((_, entry) <- theories.toList)
        yield ((entry.name, ()), entry.header.imports.map(imp => theories(imp.theory).name)))

    def get_file(file: JFile, bootstrap: Boolean = false): Option[Document.Node.Name] =
    {
      val res = files.getOrElse(File.canonical(file), Nil).headOption
      if (bootstrap) res.map(_.map_theory(Thy_Header.bootstrap_name(_))) else res
    }
  }

  object Base
  {
    def bootstrap(global_theories: Map[String, String]): Base =
      Base(
        global_theories = global_theories,
        overall_syntax = Thy_Header.bootstrap_syntax)
  }

  sealed case class Base(
    pos: Position.T = Position.none,
    doc_names: List[String] = Nil,
    global_theories: Map[String, String] = Map.empty,
    loaded_theories: Graph[String, Outer_Syntax] = Graph.string,
    used_theories: List[((Document.Node.Name, Options), List[Document.Node.Name])] = Nil,
    dump_checkpoints: Set[Document.Node.Name] = Set.empty,
    known: Known = Known.empty,
    overall_syntax: Outer_Syntax = Outer_Syntax.empty,
    imported_sources: List[(Path, SHA1.Digest)] = Nil,
    sources: List[(Path, SHA1.Digest)] = Nil,
    session_graph_display: Graph_Display.Graph = Graph_Display.empty_graph,
    errors: List[String] = Nil,
    imports: Option[Base] = None)
  {
    override def toString: String =
      "Sessions.Base(loaded_theories = " + loaded_theories.size +
        ", used_theories = " + used_theories.length + ")"

    def platform_path: Base = copy(known = known.platform_path)
    def standard_path: Base = copy(known = known.standard_path)

    def theory_qualifier(name: String): String =
      global_theories.getOrElse(name, Long_Name.qualifier(name))
    def theory_qualifier(name: Document.Node.Name): String = theory_qualifier(name.theory)

    def loaded_theory(name: String): Boolean = loaded_theories.defined(name)
    def loaded_theory(name: Document.Node.Name): Boolean = loaded_theory(name.theory)

    def loaded_theory_syntax(name: String): Option[Outer_Syntax] =
      if (loaded_theory(name)) Some(loaded_theories.get_node(name)) else None
    def loaded_theory_syntax(name: Document.Node.Name): Option[Outer_Syntax] =
      loaded_theory_syntax(name.theory)

    def node_syntax(nodes: Document.Nodes, name: Document.Node.Name): Outer_Syntax =
      nodes(name).syntax orElse loaded_theory_syntax(name) getOrElse overall_syntax

    def known_theory(name: String): Option[Document.Node.Name] =
      known.theories.get(name).map(_.name)

    def dest_known_theories: List[(String, String)] =
      for ((theory, entry) <- known.theories.toList)
        yield (theory, entry.name.node)

    def get_imports: Base = imports getOrElse Base.bootstrap(global_theories)
  }

  sealed case class Deps(
    sessions_structure: Structure, session_bases: Map[String, Base], all_known: Known)
  {
    override def toString: String = "Sessions.Deps(" + sessions_structure + ")"

    def is_empty: Boolean = session_bases.isEmpty
    def apply(name: String): Base = session_bases(name)
    def get(name: String): Option[Base] = session_bases.get(name)

    def imported_sources(name: String): List[SHA1.Digest] =
      session_bases(name).imported_sources.map(_._2)

    def dump_checkpoints: Set[Document.Node.Name] =
      (for {
        (_, base) <- session_bases.iterator
        name <- base.dump_checkpoints.iterator
      } yield name).toSet

    def used_theories_condition(
      default_options: Options, progress: Progress = No_Progress): Document.Theory_Graph[Options] =
    {
      val default_skip_proofs = default_options.bool("skip_proofs")
      Document.theory_graph(
        permissive = true,
        entries =
          for {
            session_name <- sessions_structure.build_topological_order
            entry @ ((name, options), _) <- session_bases(session_name).used_theories
            if {
              def warn(msg: String): Unit =
                progress.echo_warning("Skipping theory " + name + "  (" + msg + ")")

              val conditions =
                space_explode(',', options.string("condition")).
                  filter(cond => Isabelle_System.getenv(cond) == "")
              if (conditions.nonEmpty) {
                warn("undefined " + conditions.mkString(", "))
                false
              }
              else if (default_skip_proofs && !options.bool("skip_proofs")) {
                warn("option skip_proofs")
                false
              }
              else true
            }
          } yield entry)
    }

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
      global_theories: Map[String, String],
      progress: Progress = No_Progress,
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

    val doc_names = Doc.doc_names()

    val session_bases =
      (Map.empty[String, Base] /: sessions_structure.imports_topological_order)({
        case (session_bases, session_name) =>
          progress.expose_interrupt()

          val info = sessions_structure(session_name)
          try {
            val parent_base: Sessions.Base =
              info.parent match {
                case None => Base.bootstrap(global_theories)
                case Some(parent) => session_bases(parent)
              }
            val imports_base: Sessions.Base =
              parent_base.copy(known =
                Known.make(info.dir, parent_base :: info.imports.map(session_bases(_))))

            val resources = new Resources(imports_base)

            if (verbose || list_files) {
              val groups =
                if (info.groups.isEmpty) ""
                else info.groups.mkString(" (", " ", ")")
              progress.echo("Session " + info.chapter + "/" + info.name + groups)
            }

            val dependencies = resources.session_dependencies(info)

            val dump_checkpoints = resources.dump_checkpoints(info)

            val overall_syntax = dependencies.overall_syntax

            val theory_files = dependencies.theories.map(_.path)
            val loaded_files =
              if (inlined_files) dependencies.loaded_files(Sessions.is_pure(info.name))
              else Nil

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
                val qualifier = imports_base.theory_qualifier(name)
                if (qualifier == info.name)
                  Graph_Display.Node(name.theory_base_name, "theory." + name.theory)
                else session_node(qualifier)
              }

              val imports_subgraph =
                sessions_structure.imports_graph.
                  restrict(sessions_structure.imports_graph.all_preds(info.deps).toSet)

              val graph0 =
                (Graph_Display.empty_graph /: imports_subgraph.topological_order)(
                  { case (g, session) =>
                      val a = session_node(session)
                      val bs = imports_subgraph.imm_preds(session).toList.map(session_node(_))
                      ((g /: (a :: bs))(_.default_node(_, Nil)) /: bs)(_.add_edge(_, a)) })

              (graph0 /: dependencies.entries)(
                { case (g, entry) =>
                    val a = node(entry.name)
                    val bs = entry.header.imports.map(node).filterNot(_ == a)
                    ((g /: (a :: bs))(_.default_node(_, Nil)) /: bs)(_.add_edge(_, a)) })
            }

            val known =
              Known.make(info.dir, List(imports_base),
                sessions = List(info.name -> info.pos),
                theories = dependencies.entries,
                loaded_files = loaded_files)

            val used_theories =
              for ((options, name) <- dependencies.adjunct_theories)
              yield ((name, options), known.theories(name.theory).header.imports)

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
                doc_names = doc_names,
                global_theories = global_theories,
                loaded_theories = dependencies.loaded_theories,
                used_theories = used_theories,
                dump_checkpoints = dump_checkpoints,
                known = known,
                overall_syntax = overall_syntax,
                imported_sources = check_sources(imported_files),
                sources = check_sources(session_files),
                session_graph_display = session_graph_display,
                errors = dependencies.errors ::: sources_errors ::: path_errors ::: bibtex_errors,
                imports = Some(imports_base))

            session_bases + (info.name -> base)
          }
          catch {
            case ERROR(msg) =>
              cat_error(msg, "The error(s) above occurred in session " +
                quote(info.name) + Position.here(info.pos))
          }
      })

    val all_known =
      Known.make(Path.current, sessions_structure.imports_topological_order.map(session_bases(_)))

    Deps(sessions_structure, session_bases, all_known)
  }


  /* base info */

  sealed case class Base_Info(
    options: Options,
    dirs: List[Path],
    session: String,
    sessions_structure: Structure,
    errors: List[String],
    base: Base,
    infos: List[Info])
  {
    def check_base: Base = if (errors.isEmpty) base else error(cat_lines(errors))
  }

  def base_info(options: Options,
    session: String,
    progress: Progress = No_Progress,
    dirs: List[Path] = Nil,
    include_sessions: List[String] = Nil,
    session_ancestor: Option[String] = None,
    session_requirements: Boolean = false,
    session_focus: Boolean = false,
    all_known: Boolean = false): Base_Info =
  {
    val full_sessions = load_structure(options, dirs = dirs)
    val global_theories = full_sessions.global_theories

    val selected_sessions =
      full_sessions.selection(Selection(sessions = session :: session_ancestor.toList))
    val info = selected_sessions(session)
    val ancestor = session_ancestor orElse info.parent

    val (session1, infos1) =
      if (session_requirements && ancestor.isDefined) {
        val deps = Sessions.deps(selected_sessions, global_theories, progress = progress)
        val base = deps(session)

        val ancestor_loaded =
          deps.get(ancestor.get) match {
            case Some(ancestor_base)
            if !selected_sessions.imports_requirements(List(ancestor.get)).contains(session) =>
              ancestor_base.loaded_theories.defined(_)
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
          (other_name,
            List(
              make_info(info.options,
                dir_selected = false,
                dir = info.dir,
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
                  theories = List((Nil, required_theories.map(thy => ((thy, Position.none), false)))),
                  document_files = Nil,
                  export_files = Nil))))
        }
      }
      else (session, Nil)

    val full_sessions1 =
      if (infos1.isEmpty) full_sessions
      else load_structure(options, dirs = dirs, infos = infos1)

    val selected_sessions1 =
    {
      val sel_sessions1 = session1 :: session :: include_sessions
      val select_sessions1 =
        if (session_focus) {
          full_sessions1.check_sessions(sel_sessions1)
          full_sessions1.imports_descendants(sel_sessions1)
        }
        else sel_sessions1
      full_sessions1.selection(Selection(sessions = select_sessions1))
    }

    val sessions1 = if (all_known) full_sessions1 else selected_sessions1
    val deps1 = Sessions.deps(sessions1, global_theories, progress = progress)
    val base1 = deps1(session1).copy(known = deps1.all_known)

    Base_Info(options, dirs, session1, deps1.sessions_structure, deps1.errors, base1, infos1)
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
    options: Options,
    imports: List[String],
    theories: List[(Options, List[(String, Position.T)])],
    global_theories: List[String],
    document_files: List[(Path, Path)],
    export_files: List[(Path, Int, List[String])],
    meta_digest: SHA1.Digest)
  {
    def deps: List[String] = parent.toList ::: imports

    def timeout: Time = Time.seconds(options.real("timeout") * options.real("timeout_scale"))

    def bibtex_entries: List[Text.Info[String]] =
      (for {
        (document_dir, file) <- document_files.iterator
        if Bibtex.is_bibtex(file.file_name)
        info <- Bibtex.entries(File.read(dir + document_dir + file)).iterator
      } yield info).toList
  }

  def make_info(options: Options, dir_selected: Boolean, dir: Path, chapter: String,
    entry: Session_Entry): Info =
  {
    try {
      val name = entry.name

      if (exclude_session(name)) error("Bad session name")
      if (is_pure(name) && entry.parent.isDefined) error("Illegal parent session")
      if (!is_pure(name) && !entry.parent.isDefined) error("Missing parent session")

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
        SHA1.digest((name, chapter, entry.parent, entry.options, entry.imports,
          entry.theories_no_position, conditions, entry.document_files).toString)

      Info(name, chapter, dir_selected, entry.pos, entry.groups,
        dir + Path.explode(entry.path), entry.parent, entry.description, session_options,
        entry.imports, theories, global_theories, document_files, export_files, meta_digest)
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

  def make(infos: List[Info]): Structure =
  {
    def add_edges(graph: Graph[String, Info], kind: String, edges: Info => Traversable[String])
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
      (graph /: graph.iterator) {
        case (g, (name, (info, _))) => (g /: edges(info))(add_edge(info.pos, name, _, _))
      }
    }

    val graph0 =
      (Graph.string[Info] /: infos) {
        case (graph, info) =>
          if (graph.defined(info.name))
            error("Duplicate session " + quote(info.name) + Position.here(info.pos) +
              Position.here(graph.get_node(info.name).pos))
          else graph.new_node(info.name, info)
      }
    val graph1 = add_edges(graph0, "parent", _.parent)
    val graph2 = add_edges(graph1, "imports", _.imports)

    new Structure(graph1, graph2)
  }

  final class Structure private[Sessions](
      val build_graph: Graph[String, Info],
      val imports_graph: Graph[String, Info])
  {
    sessions_structure =>

    lazy val chapters: SortedMap[String, List[Info]] =
      (SortedMap.empty[String, List[Info]] /: build_graph.iterator)(
        { case (chs, (_, (info, _))) =>
            chs + (info.chapter -> (info :: chs.getOrElse(info.chapter, Nil))) })

    def build_graph_display: Graph_Display.Graph = Graph_Display.make_graph(build_graph)
    def imports_graph_display: Graph_Display.Graph = Graph_Display.make_graph(imports_graph)

    def defined(name: String): Boolean = imports_graph.defined(name)
    def apply(name: String): Info = imports_graph.get_node(name)
    def get(name: String): Option[Info] = if (defined(name)) Some(apply(name)) else None

    def global_theories: Map[String, String] =
      (Thy_Header.bootstrap_global_theories.toMap /:
        (for {
          (_, (info, _)) <- imports_graph.iterator
          thy <- info.global_theories.iterator }
         yield (thy, info)))({
            case (global, (thy, info)) =>
              val qualifier = info.name
              global.get(thy) match {
                case Some(qualifier1) if qualifier != qualifier1 =>
                  error("Duplicate global theory " + quote(thy) + Position.here(info.pos))
                case _ => global + (thy -> qualifier)
              }
          })

    def check_sessions(names: List[String])
    {
      val bad_sessions = SortedSet(names.filterNot(defined(_)): _*).toList
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

      new Structure(restrict(build_graph), restrict(imports_graph))
    }

    def selection_deps(
      options: Options,
      selection: Selection,
      progress: Progress = No_Progress,
      uniform_session: Boolean = false,
      loading_sessions: Boolean = false,
      inlined_files: Boolean = false,
      verbose: Boolean = false): Deps =
    {
      val selection1 =
        if (uniform_session) {
          val sessions_structure1 = sessions_structure.selection(selection)

          val default_record_proofs = options.int("record_proofs")
          val sessions_record_proofs =
            for {
              name <- sessions_structure1.build_topological_order
              info <- sessions_structure1.get(name)
              if info.options.int("record_proofs") > default_record_proofs
            } yield name

          val excluded =
            for (name <- sessions_structure1.build_descendants(sessions_record_proofs))
            yield {
              progress.echo_warning("Skipping session " + name + "  (option record_proofs)")
              name
            }

          selection.copy(exclude_sessions = excluded ::: selection.exclude_sessions)
        }
        else selection

      val deps =
        Sessions.deps(sessions_structure.selection(selection1), global_theories,
          progress = progress, inlined_files = inlined_files, verbose = verbose)

      if (loading_sessions) {
        val selection_size = deps.sessions_structure.build_graph.size
        if (selection_size > 1) progress.echo("Loading " + selection_size + " sessions ...")
      }

      deps
    }

    def build_selection(sel: Selection): List[String] = selected(build_graph, sel)
    def build_descendants(ss: List[String]): List[String] = build_graph.all_succs(ss)
    def build_requirements(ss: List[String]): List[String] = build_graph.all_preds(ss).reverse
    def build_topological_order: List[String] = build_graph.topological_order

    def imports_selection(sel: Selection): List[String] = selected(imports_graph, sel)
    def imports_descendants(ss: List[String]): List[String] = imports_graph.all_succs(ss)
    def imports_requirements(ss: List[String]): List[String] = imports_graph.all_preds(ss).reverse
    def imports_topological_order: List[String] = imports_graph.topological_order

    override def toString: String =
      imports_graph.keys_iterator.mkString("Sessions.Structure(", ", ", ")")
  }


  /* parser */

  val ROOT = Path.explode("ROOT")
  val ROOTS = Path.explode("ROOTS")

  private val CHAPTER = "chapter"
  private val SESSION = "session"
  private val IN = "in"
  private val DESCRIPTION = "description"
  private val OPTIONS = "options"
  private val SESSIONS = "sessions"
  private val THEORIES = "theories"
  private val GLOBAL = "global"
  private val DOCUMENT_FILES = "document_files"
  private val EXPORT_FILES = "export_files"

  val root_syntax =
    Outer_Syntax.empty + "(" + ")" + "+" + "," + "=" + "[" + "]" + GLOBAL + IN +
      (CHAPTER, Keyword.THY_DECL) +
      (SESSION, Keyword.THY_DECL) +
      (DESCRIPTION, Keyword.QUASI_COMMAND) +
      (OPTIONS, Keyword.QUASI_COMMAND) +
      (SESSIONS, Keyword.QUASI_COMMAND) +
      (THEORIES, Keyword.QUASI_COMMAND) +
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
    theories: List[(List[Options.Spec], List[((String, Position.T), Boolean)])],
    document_files: List[(String, String)],
    export_files: List[(String, Int, List[String])]) extends Entry
  {
    def theories_no_position: List[(List[Options.Spec], List[(String, Boolean)])] =
      theories.map({ case (a, b) => (a, b.map({ case ((c, _), d) => (c, d) })) })
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

      val global =
        ($$$("(") ~! $$$(GLOBAL) ~ $$$(")")) ^^ { case _ => true } | success(false)

      val theory_entry =
        position(theory_name) ~ global ^^ { case x ~ y => (x, y) }

      val theories =
        $$$(THEORIES) ~!
          ((options | success(Nil)) ~ rep1(theory_entry)) ^^
          { case _ ~ (x ~ y) => (x, y) }

      val in_path = $$$("(") ~! ($$$(IN) ~ path ~ $$$(")")) ^^ { case _ ~ (_ ~ x ~ _) => x }

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
              rep(theories) ~
              (rep(document_files) ^^ (x => x.flatten)) ~
              (rep(export_files))))) ^^
        { case _ ~ ((a, pos) ~ b ~ c ~ (_ ~ (d ~ e ~ f ~ g ~ h ~ i ~ j))) =>
            Session_Entry(pos, a, b, c, d, e, f, g, h, i, j) }
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

  private def is_session_dir(dir: Path): Boolean =
    (dir + ROOT).is_file || (dir + ROOTS).is_file

  private def check_session_dir(dir: Path): Path =
    if (is_session_dir(dir)) File.pwd() + dir.expand
    else error("Bad session root directory: " + dir.toString)

  def directories(dirs: List[Path], select_dirs: List[Path]): List[(Boolean, Path)] =
  {
    val default_dirs = Isabelle_System.components().filter(is_session_dir(_))
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
      ((Map.empty[JFile, (Boolean, Path)] /: roots) { case (m, (select, path)) =>
        val file = path.canonical_file
        m.get(file) match {
          case None => m + (file -> (select, path))
          case Some((select1, path1)) => m + (file -> (select1 || select, path1))
        }
      }).toList.map(_._2)

    make(unique_roots.flatMap(p => read_root(options, p._1, p._2)) ::: infos)
  }



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

  def store(options: Options): Store = new Store(options)

  class Store private[Sessions](val options: Options)
  {
    override def toString: String = "Store(output_dir = " + output_dir.expand + ")"


    /* directories */

    val system_output_dir: Path = Path.explode("$ISABELLE_HEAPS_SYSTEM/$ML_IDENTIFIER")
    val user_output_dir: Path = Path.explode("$ISABELLE_HEAPS/$ML_IDENTIFIER")

    def system_heaps: Boolean = options.bool("system_heaps")

    val output_dir: Path =
      if (system_heaps) system_output_dir else user_output_dir

    val input_dirs: List[Path] =
      if (system_heaps) List(system_output_dir)
      else List(user_output_dir, system_output_dir)

    val browser_info: Path =
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

    def prepare_output_dir() { Isabelle_System.mkdirs(output_dir + Path.basic("log")) }


    /* heap */

    def find_heap(name: String): Option[Path] =
      input_dirs.map(_ + heap(name)).find(_.is_file)

    def find_heap_digest(name: String): Option[String] =
      find_heap(name).flatMap(read_heap_digest(_))

    def the_heap(name: String): Path =
      find_heap(name) getOrElse
        error("Missing heap image for session " + quote(name) + " -- expected in:\n" +
          cat_lines(input_dirs.map(dir => "  " + dir.expand.implode)))


    /* database */

    private def database_server: Boolean = options.bool("build_database_server")

    def access_database(name: String, output: Boolean = false): Option[SQL.Database] =
    {
      if (database_server) {
        val db =
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
        if (output || has_session_info(db, name)) Some(db) else { db.close; None }
      }
      else if (output) Some(SQLite.open_database(output_database(name)))
      else input_dirs.map(_ + database(name)).find(_.is_file).map(SQLite.open_database(_))
    }

    def open_database(name: String, output: Boolean = false): SQL.Database =
      access_database(name, output = output) getOrElse
        error("Missing build database for session " + quote(name))

    def clean_output(name: String): (Boolean, Boolean) =
    {
      val relevant_db =
        database_server &&
        {
          access_database(name) match {
            case Some(db) =>
              try {
                db.transaction {
                  val relevant_db = has_session_info(db, name)
                  init_session_info(db, name)
                  relevant_db
                }
              } finally { db.close }
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

    val xml_cache: XML.Cache = XML.make_cache()
    val xz_cache: XZ.Cache = XZ.make_cache()

    def read_bytes(db: SQL.Database, name: String, column: SQL.Column): Bytes =
      db.using_statement(Session_Info.table.select(List(column),
        Session_Info.session_name.where_equal(name)))(stmt =>
      {
        val res = stmt.execute_query()
        if (!res.next()) Bytes.empty else res.bytes(column)
      })

    def read_properties(db: SQL.Database, name: String, column: SQL.Column): List[Properties.T] =
      Properties.uncompress(
        read_bytes(db, name, column), cache = xz_cache, xml_cache = Some(xml_cache))


    /* session info */

    def init_session_info(db: SQL.Database, name: String)
    {
      db.transaction {
        db.create_table(Session_Info.table)
        db.using_statement(
          Session_Info.table.delete(Session_Info.session_name.where_equal(name)))(_.execute)

        db.create_table(Export.Data.table)
        db.using_statement(
          Export.Data.table.delete(Export.Data.session_name.where_equal(name)))(_.execute)
      }
    }

    def has_session_info(db: SQL.Database, name: String): Boolean =
    {
      db.transaction {
        db.tables.contains(Session_Info.table.name) &&
        {
          db.using_statement(
            Session_Info.table.select(List(Session_Info.session_name),
              Session_Info.session_name.where_equal(name)))(stmt => stmt.execute_query().next())
        }
      }
    }

    def write_session_info(
      db: SQL.Database,
      name: String,
      build_log: Build_Log.Session_Info,
      build: Build.Session_Info)
    {
      db.transaction {
        db.using_statement(Session_Info.table.insert())(stmt =>
        {
          stmt.string(1) = name
          stmt.bytes(2) = Properties.encode(build_log.session_timing)
          stmt.bytes(3) = Properties.compress(build_log.command_timings, cache = xz_cache)
          stmt.bytes(4) = Properties.compress(build_log.theory_timings, cache = xz_cache)
          stmt.bytes(5) = Properties.compress(build_log.ml_statistics, cache = xz_cache)
          stmt.bytes(6) = Properties.compress(build_log.task_statistics, cache = xz_cache)
          stmt.bytes(7) = Build_Log.compress_errors(build_log.errors, cache = xz_cache)
          stmt.string(8) = build.sources
          stmt.string(9) = cat_lines(build.input_heaps)
          stmt.string(10) = build.output_heap getOrElse ""
          stmt.int(11) = build.return_code
          stmt.execute()
        })
      }
    }

    def read_session_timing(db: SQL.Database, name: String): Properties.T =
      Properties.decode(read_bytes(db, name, Session_Info.session_timing), Some(xml_cache))

    def read_command_timings(db: SQL.Database, name: String): List[Properties.T] =
      read_properties(db, name, Session_Info.command_timings)

    def read_theory_timings(db: SQL.Database, name: String): List[Properties.T] =
      read_properties(db, name, Session_Info.theory_timings)

    def read_ml_statistics(db: SQL.Database, name: String): List[Properties.T] =
      read_properties(db, name, Session_Info.ml_statistics)

    def read_task_statistics(db: SQL.Database, name: String): List[Properties.T] =
      read_properties(db, name, Session_Info.task_statistics)

    def read_errors(db: SQL.Database, name: String): List[String] =
      Build_Log.uncompress_errors(read_bytes(db, name, Session_Info.errors), cache = xz_cache)

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
