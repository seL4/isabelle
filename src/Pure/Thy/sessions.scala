/*  Title:      Pure/Thy/sessions.scala
    Author:     Makarius

Isabelle session information.
*/

package isabelle

import java.nio.ByteBuffer
import java.nio.channels.FileChannel
import java.nio.file.StandardOpenOption

import scala.collection.SortedSet
import scala.collection.mutable


object Sessions
{
  /* Pure */

  def pure_name(name: String): Boolean = name == Thy_Header.PURE

  def pure_files(resources: Resources, syntax: Outer_Syntax, dir: Path): List[Path] =
  {
    val roots = Thy_Header.ml_roots.map(_._1)
    val loaded_files =
      roots.flatMap(root => resources.loaded_files(syntax, File.read(dir + Path.explode(root))))
    (roots ::: loaded_files).map(file => dir + Path.explode(file))
  }

  def pure_base(options: Options): Base = session_base(options, Thy_Header.PURE)


  /* base info and source dependencies */

  object Base
  {
    lazy val bootstrap: Base =
      Base(keywords = Thy_Header.bootstrap_header, syntax = Thy_Header.bootstrap_syntax)
  }

  sealed case class Base(
    loaded_theories: Set[String] = Set.empty,
    known_theories: Map[String, Document.Node.Name] = Map.empty,
    keywords: Thy_Header.Keywords = Nil,
    syntax: Outer_Syntax = Outer_Syntax.empty,
    sources: List[(Path, SHA1.Digest)] = Nil,
    session_graph: Graph_Display.Graph = Graph_Display.empty_graph)

  sealed case class Deps(deps: Map[String, Base])
  {
    def is_empty: Boolean = deps.isEmpty
    def apply(name: String): Base = deps(name)
    def sources(name: String): List[SHA1.Digest] = deps(name).sources.map(_._2)
  }

  def dependencies(
      progress: Progress = No_Progress,
      inlined_files: Boolean = false,
      verbose: Boolean = false,
      list_files: Boolean = false,
      check_keywords: Set[String] = Set.empty,
      tree: Tree): Deps =
    Deps((Map.empty[String, Base] /: tree.topological_order)(
      { case (deps, (name, info)) =>
          if (progress.stopped) throw Exn.Interrupt()

          try {
            val resources =
              new Resources(
                info.parent match {
                  case None => Base.bootstrap
                  case Some(parent) => deps(parent)
                })

            if (verbose || list_files) {
              val groups =
                if (info.groups.isEmpty) ""
                else info.groups.mkString(" (", " ", ")")
              progress.echo("Session " + info.chapter + "/" + name + groups)
            }

            val thy_deps =
            {
              val root_theories =
                info.theories.flatMap({
                  case (global, _, thys) =>
                    thys.map(thy =>
                      (resources.node_name(
                        if (global) "" else name, info.dir + resources.thy_path(thy)), info.pos))
                })
              val thy_deps = resources.thy_info.dependencies(name, root_theories)

              thy_deps.errors match {
                case Nil => thy_deps
                case errs => error(cat_lines(errs))
              }
            }

            val known_theories =
              (resources.base.known_theories /: thy_deps.deps)({ case (known, dep) =>
                val name = dep.name
                known.get(name.theory) match {
                  case Some(name1) if name != name1 =>
                    error("Duplicate theory " + quote(name.node) + " vs. " + quote(name1.node))
                  case _ =>
                    known + (name.theory -> name) + (Long_Name.base_name(name.theory) -> name)
                }
              })

            val loaded_theories = thy_deps.loaded_theories
            val keywords = thy_deps.keywords
            val syntax = thy_deps.syntax

            val theory_files = thy_deps.deps.map(dep => Path.explode(dep.name.node))
            val loaded_files =
              if (inlined_files) {
                val pure_files =
                  if (pure_name(name)) Sessions.pure_files(resources, syntax, info.dir)
                  else Nil
                pure_files ::: thy_deps.loaded_files
              }
              else Nil

            val all_files =
              (theory_files ::: loaded_files :::
                info.files.map(file => info.dir + file) :::
                info.document_files.map(file => info.dir + file._1 + file._2)).map(_.expand)

            if (list_files)
              progress.echo(cat_lines(all_files.map(_.implode).sorted.map("  " + _)))

            if (check_keywords.nonEmpty)
              Check_Keywords.check_keywords(progress, syntax.keywords, check_keywords, theory_files)

            val sources = all_files.map(p => (p, SHA1.digest(p.file)))

            val session_graph =
              Present.session_graph(info.parent getOrElse "",
                resources.base.loaded_theories, thy_deps.deps)

            val base =
              Base(loaded_theories, known_theories, keywords, syntax, sources, session_graph)
            deps + (name -> base)
          }
          catch {
            case ERROR(msg) =>
              cat_error(msg, "The error(s) above occurred in session " +
                quote(name) + Position.here(info.pos))
          }
      }))

  def session_base(options: Options, session: String, dirs: List[Path] = Nil): Base =
  {
    val (_, tree) = load(options, dirs = dirs).selection(sessions = List(session))
    dependencies(tree = tree)(session)
  }


  /* session tree */

  sealed case class Info(
    chapter: String,
    select: Boolean,
    pos: Position.T,
    groups: List[String],
    dir: Path,
    parent: Option[String],
    description: String,
    options: Options,
    theories: List[(Boolean, Options, List[Path])],
    files: List[Path],
    document_files: List[(Path, Path)],
    meta_digest: SHA1.Digest)
  {
    def timeout: Time = Time.seconds(options.real("timeout") * options.real("timeout_scale"))
  }

  object Tree
  {
    def apply(infos: Seq[(String, Info)]): Tree =
    {
      val graph1 =
        (Graph.string[Info] /: infos) {
          case (graph, (name, info)) =>
            if (graph.defined(name))
              error("Duplicate session " + quote(name) + Position.here(info.pos) +
                Position.here(graph.get_node(name).pos))
            else graph.new_node(name, info)
        }
      val graph2 =
        (graph1 /: graph1.iterator) {
          case (graph, (name, (info, _))) =>
            info.parent match {
              case None => graph
              case Some(parent) =>
                if (!graph.defined(parent))
                  error("Bad parent session " + quote(parent) + " for " +
                    quote(name) + Position.here(info.pos))

                try { graph.add_edge_acyclic(parent, name) }
                catch {
                  case exn: Graph.Cycles[_] =>
                    error(cat_lines(exn.cycles.map(cycle =>
                      "Cyclic session dependency of " +
                        cycle.map(c => quote(c.toString)).mkString(" via "))) +
                          Position.here(info.pos))
                }
            }
        }
      new Tree(graph2)
    }
  }

  final class Tree private(val graph: Graph[String, Info])
    extends PartialFunction[String, Info]
  {
    def apply(name: String): Info = graph.get_node(name)
    def isDefinedAt(name: String): Boolean = graph.defined(name)

    def selection(
      requirements: Boolean = false,
      all_sessions: Boolean = false,
      exclude_session_groups: List[String] = Nil,
      exclude_sessions: List[String] = Nil,
      session_groups: List[String] = Nil,
      sessions: List[String] = Nil): (List[String], Tree) =
    {
      val bad_sessions =
        SortedSet((exclude_sessions ::: sessions).filterNot(isDefinedAt(_)): _*).toList
      if (bad_sessions.nonEmpty) error("Undefined session(s): " + commas_quote(bad_sessions))

      val excluded =
      {
        val exclude_group = exclude_session_groups.toSet
        val exclude_group_sessions =
          (for {
            (name, (info, _)) <- graph.iterator
            if apply(name).groups.exists(exclude_group)
          } yield name).toList
        graph.all_succs(exclude_group_sessions ::: exclude_sessions).toSet
      }

      val pre_selected =
      {
        if (all_sessions) graph.keys
        else {
          val select_group = session_groups.toSet
          val select = sessions.toSet
          (for {
            (name, (info, _)) <- graph.iterator
            if info.select || select(name) || apply(name).groups.exists(select_group)
          } yield name).toList
        }
      }.filterNot(excluded)

      val selected =
        if (requirements) (graph.all_preds(pre_selected).toSet -- pre_selected).toList
        else pre_selected

      val graph1 = graph.restrict(graph.all_preds(selected).toSet)
      (selected, new Tree(graph1))
    }

    def ancestors(name: String): List[String] =
      graph.all_preds(List(name)).tail.reverse

    def topological_order: List[(String, Info)] =
      graph.topological_order.map(name => (name, apply(name)))

    override def toString: String = graph.keys_iterator.mkString("Sessions.Tree(", ", ", ")")
  }


  /* parser */

  val ROOT = Path.explode("ROOT")
  val ROOTS = Path.explode("ROOTS")

  private val CHAPTER = "chapter"
  private val SESSION = "session"
  private val IN = "in"
  private val DESCRIPTION = "description"
  private val OPTIONS = "options"
  private val GLOBAL_THEORIES = "global_theories"
  private val THEORIES = "theories"
  private val FILES = "files"
  private val DOCUMENT_FILES = "document_files"

  lazy val root_syntax =
    Outer_Syntax.init() + "(" + ")" + "+" + "," + "=" + "[" + "]" + IN +
      (CHAPTER, Keyword.THY_DECL) +
      (SESSION, Keyword.THY_DECL) +
      (DESCRIPTION, Keyword.QUASI_COMMAND) +
      (OPTIONS, Keyword.QUASI_COMMAND) +
      (GLOBAL_THEORIES, Keyword.QUASI_COMMAND) +
      (THEORIES, Keyword.QUASI_COMMAND) +
      (FILES, Keyword.QUASI_COMMAND) +
      (DOCUMENT_FILES, Keyword.QUASI_COMMAND)

  private object Parser extends Parse.Parser with Options.Parser
  {
    private abstract class Entry
    private sealed case class Chapter(name: String) extends Entry
    private sealed case class Session_Entry(
      pos: Position.T,
      name: String,
      groups: List[String],
      path: String,
      parent: Option[String],
      description: String,
      options: List[Options.Spec],
      theories: List[(Boolean, List[Options.Spec], List[String])],
      files: List[String],
      document_files: List[(String, String)]) extends Entry

    private val chapter: Parser[Chapter] =
    {
      val chapter_name = atom("chapter name", _.is_name)

      command(CHAPTER) ~! chapter_name ^^ { case _ ~ a => Chapter(a) }
    }

    private val session_entry: Parser[Session_Entry] =
    {
      val session_name = atom("session name", _.is_name)

      val option =
        option_name ~ opt($$$("=") ~! option_value ^^
          { case _ ~ x => x }) ^^ { case x ~ y => (x, y) }
      val options = $$$("[") ~> rep1sep(option, $$$(",")) <~ $$$("]")

      val theories =
        ($$$(GLOBAL_THEORIES) | $$$(THEORIES)) ~!
          ((options | success(Nil)) ~ rep(theory_name)) ^^
          { case x ~ (y ~ z) => (x == GLOBAL_THEORIES, y, z) }

      val document_files =
        $$$(DOCUMENT_FILES) ~!
          (($$$("(") ~! ($$$(IN) ~! (path ~ $$$(")"))) ^^
              { case _ ~ (_ ~ (x ~ _)) => x } | success("document")) ~
            rep1(path)) ^^ { case _ ~ (x ~ y) => y.map((x, _)) }

      command(SESSION) ~!
        (position(session_name) ~
          (($$$("(") ~! (rep1(name) <~ $$$(")")) ^^ { case _ ~ x => x }) | success(Nil)) ~
          (($$$(IN) ~! path ^^ { case _ ~ x => x }) | success(".")) ~
          ($$$("=") ~!
            (opt(session_name ~! $$$("+") ^^ { case x ~ _ => x }) ~
              (($$$(DESCRIPTION) ~! text ^^ { case _ ~ x => x }) | success("")) ~
              (($$$(OPTIONS) ~! options ^^ { case _ ~ x => x }) | success(Nil)) ~
              rep1(theories) ~
              (($$$(FILES) ~! rep1(path) ^^ { case _ ~ x => x }) | success(Nil)) ~
              (rep(document_files) ^^ (x => x.flatten))))) ^^
        { case _ ~ ((a, pos) ~ b ~ c ~ (_ ~ (d ~ e ~ f ~ g ~ h ~ i))) =>
            Session_Entry(pos, a, b, c, d, e, f, g, h, i) }
    }

    def parse(options: Options, select: Boolean, dir: Path): List[(String, Info)] =
    {
      def make_info(entry_chapter: String, entry: Session_Entry): (String, Info) =
      {
        try {
          val name = entry.name

          if (name == "") error("Bad session name")
          if (pure_name(name) && entry.parent.isDefined) error("Illegal parent session")
          if (!pure_name(name) && !entry.parent.isDefined) error("Missing parent session")

          val session_options = options ++ entry.options

          val theories =
            entry.theories.map({ case (global, opts, thys) =>
              (global, session_options ++ opts, thys.map(Path.explode(_))) })
          val files = entry.files.map(Path.explode(_))
          val document_files =
            entry.document_files.map({ case (s1, s2) => (Path.explode(s1), Path.explode(s2)) })

          val meta_digest =
            SHA1.digest((entry_chapter, name, entry.parent, entry.options,
              entry.theories, entry.files, entry.document_files).toString)

          val info =
            Info(entry_chapter, select, entry.pos, entry.groups, dir + Path.explode(entry.path),
              entry.parent, entry.description, session_options, theories, files,
              document_files, meta_digest)

          (name, info)
        }
        catch {
          case ERROR(msg) =>
            error(msg + "\nThe error(s) above occurred in session entry " +
              quote(entry.name) + Position.here(entry.pos))
        }
      }

      val root = dir + ROOT
      if (root.is_file) {
        val toks = Token.explode(root_syntax.keywords, File.read(root))
        val start = Token.Pos.file(root.implode)

        parse_all(rep(chapter | session_entry), Token.reader(toks, start)) match {
          case Success(result, _) =>
            var entry_chapter = "Unsorted"
            val infos = new mutable.ListBuffer[(String, Info)]
            result.foreach {
              case Chapter(name) => entry_chapter = name
              case entry: Session_Entry => infos += make_info(entry_chapter, entry)
            }
            infos.toList
          case bad => error(bad.toString)
        }
      }
      else Nil
    }
  }


  /* load sessions from certain directories */

  private def is_session_dir(dir: Path): Boolean =
    (dir + ROOT).is_file || (dir + ROOTS).is_file

  private def check_session_dir(dir: Path): Path =
    if (is_session_dir(dir)) dir
    else error("Bad session root directory: " + dir.toString)

  def load(options: Options, dirs: List[Path] = Nil, select_dirs: List[Path] = Nil): Tree =
  {
    def load_dir(select: Boolean, dir: Path): List[(String, Info)] =
      load_root(select, dir) ::: load_roots(select, dir)

    def load_root(select: Boolean, dir: Path): List[(String, Info)] =
      Parser.parse(options, select, dir)

    def load_roots(select: Boolean, dir: Path): List[(String, Info)] =
    {
      val roots = dir + ROOTS
      if (roots.is_file) {
        for {
          line <- split_lines(File.read(roots))
          if !(line == "" || line.startsWith("#"))
          dir1 =
            try { check_session_dir(dir + Path.explode(line)) }
            catch {
              case ERROR(msg) =>
                error(msg + "\nThe error(s) above occurred in session catalog " + roots.toString)
            }
          info <- load_dir(select, dir1)
        } yield info
      }
      else Nil
    }

    val default_dirs = Isabelle_System.components().filter(is_session_dir(_))
    dirs.foreach(check_session_dir(_))
    select_dirs.foreach(check_session_dir(_))

    Tree(
      for {
        (select, dir) <- (default_dirs ::: dirs).map((false, _)) ::: select_dirs.map((true, _))
        info <- load_dir(select, dir)
      } yield info)
  }



  /** heap file with SHA1 digest **/

  private val sha1_prefix = "SHA1:"

  def read_heap_digest(heap: Path): Option[String] =
  {
    if (heap.is_file) {
      val file = FileChannel.open(heap.file.toPath, StandardOpenOption.READ)
      try {
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
      }
      finally { file.close }
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

  def store(system_mode: Boolean = false): Store = new Store(system_mode)

  class Store private[Sessions](system_mode: Boolean)
  {
    /* file names */

    def database(name: String): Path = Path.basic("log") + Path.basic(name).ext("db")
    def log(name: String): Path = Path.basic("log") + Path.basic(name)
    def log_gz(name: String): Path = log(name).ext("gz")


    /* SQL database content */

    val xml_cache: XML.Cache = new XML.Cache()

    def encode_properties(ps: Properties.T): Bytes =
      Bytes(YXML.string_of_body(XML.Encode.properties(ps)))

    def decode_properties(bs: Bytes): Properties.T =
      xml_cache.props(XML.Decode.properties(YXML.parse_body(bs.text)))

    def compress_properties(ps: List[Properties.T], options: XZ.Options = XZ.options()): Bytes =
    {
      if (ps.isEmpty) Bytes.empty
      else Bytes(YXML.string_of_body(XML.Encode.list(XML.Encode.properties)(ps))).compress(options)
    }

    def uncompress_properties(bs: Bytes): List[Properties.T] =
    {
      if (bs.isEmpty) Nil
      else
        XML.Decode.list(XML.Decode.properties)(YXML.parse_body(bs.uncompress().text)).
          map(xml_cache.props(_))
    }

    def read_bytes(db: SQLite.Database, table: SQL.Table, column: SQL.Column): Bytes =
    {
      using(db.select_statement(table, List(column)))(stmt =>
      {
        val rs = stmt.executeQuery
        if (!rs.next) Bytes.empty
        else db.bytes(rs, column.name)
      })
    }

    def read_properties(db: SQLite.Database, table: SQL.Table, column: SQL.Column)
      : List[Properties.T] = uncompress_properties(read_bytes(db, table, column))


    /* output */

    val browser_info: Path =
      if (system_mode) Path.explode("~~/browser_info")
      else Path.explode("$ISABELLE_BROWSER_INFO")

    val output_dir: Path =
      if (system_mode) Path.explode("~~/heaps/$ML_IDENTIFIER")
      else Path.explode("$ISABELLE_OUTPUT")

    def prepare_output() { Isabelle_System.mkdirs(output_dir + Path.basic("log")) }


    /* input */

    private val input_dirs =
      if (system_mode) List(output_dir)
      else {
        val ml_ident = Path.explode("$ML_IDENTIFIER").expand
        output_dir :: Path.split(Isabelle_System.getenv_strict("ISABELLE_PATH")).map(_ + ml_ident)
      }

    def find(name: String): Option[(Path, Option[String])] =
      input_dirs.find(dir => (dir + log_gz(name)).is_file).map(dir =>
        (dir + log_gz(name), read_heap_digest(dir + Path.basic(name))))

    def find_database(name: String): Option[Path] =
      input_dirs.map(_ + database(name)).find(_.is_file)

    def find_log(name: String): Option[Path] =
      input_dirs.map(_ + log(name)).find(_.is_file)

    def find_log_gz(name: String): Option[Path] =
      input_dirs.map(_ + log_gz(name)).find(_.is_file)

    def heap(name: String): Path =
      input_dirs.map(_ + Path.basic(name)).find(_.is_file) getOrElse
        error("Unknown logic " + quote(name) + " -- no heap file found in:\n" +
          cat_lines(input_dirs.map(dir => "  " + dir.expand.implode)))


    /* print */

    override def toString: String = "Store(output_dir = " + output_dir.expand + ")"
  }


  /* session info */

  object Session_Info
  {
    // Build_Log.Session_Info
    val session_name = SQL.Column.string("session_name")
    val session_timing = SQL.Column.bytes("session_timing")
    val command_timings = SQL.Column.bytes("command_timings")
    val ml_statistics = SQL.Column.bytes("ml_statistics")
    val task_statistics = SQL.Column.bytes("task_statistics")
    val build_log_columns =
      List(session_name, session_timing, command_timings, ml_statistics, task_statistics)

    // Build.Session_Info
    val sources = SQL.Column.string("sources")
    val input_heaps = SQL.Column.string("input_heaps")
    val output_heap = SQL.Column.string("output_heap")
    val return_code = SQL.Column.int("return_code")
    val build_columns = List(sources, input_heaps, output_heap, return_code)

    val table = SQL.Table("isabelle_session_info", build_log_columns ::: build_columns)

    def write(store: Store, db: SQLite.Database,
      build_log: Build_Log.Session_Info, build: Build.Session_Info)
    {
      db.transaction {
        db.drop_table(table)
        db.create_table(table)
        using(db.insert_statement(table))(stmt =>
        {
          db.set_string(stmt, 1, build_log.session_name)
          db.set_bytes(stmt, 2, store.encode_properties(build_log.session_timing))
          db.set_bytes(stmt, 3, store.compress_properties(build_log.command_timings))
          db.set_bytes(stmt, 4, store.compress_properties(build_log.ml_statistics))
          db.set_bytes(stmt, 5, store.compress_properties(build_log.task_statistics))
          db.set_string(stmt, 6, cat_lines(build.sources))
          db.set_string(stmt, 7, cat_lines(build.input_heaps))
          db.set_string(stmt, 8, build.output_heap)
          db.set_int(stmt, 9, build.return_code)
          stmt.execute()
        })
      }
    }

    def read_session_timing(store: Store, db: SQLite.Database): Properties.T =
      store.decode_properties(store.read_bytes(db, table, session_timing))

    def read_command_timings(store: Store, db: SQLite.Database): List[Properties.T] =
      store.read_properties(db, table, command_timings)

    def read_ml_statistics(store: Store, db: SQLite.Database): List[Properties.T] =
      store.read_properties(db, table, ml_statistics)

    def read_task_statistics(store: Store, db: SQLite.Database): List[Properties.T] =
      store.read_properties(db, table, task_statistics)

    def read_build_log(store: Store, db: SQLite.Database): Option[Build_Log.Session_Info] =
      using(db.select_statement(table, build_log_columns))(stmt =>
      {
        val rs = stmt.executeQuery
        if (!rs.next) None
        else {
          Some(
            Build_Log.Session_Info(
              db.string(rs, session_name.name),
              store.decode_properties(db.bytes(rs, session_timing.name)),
              store.uncompress_properties(db.bytes(rs, command_timings.name)),
              store.uncompress_properties(db.bytes(rs, ml_statistics.name)),
              store.uncompress_properties(db.bytes(rs, task_statistics.name))))
        }
      })

    def read_build(store: Store, db: SQLite.Database): Option[Build.Session_Info] =
      using(db.select_statement(table, table.columns))(stmt =>
      {
        val rs = stmt.executeQuery
        if (!rs.next) None
        else {
          Some(
            Build.Session_Info(
              split_lines(db.string(rs, sources.name)),
              split_lines(db.string(rs, input_heaps.name)),
              db.string(rs, output_heap.name),
              db.int(rs, return_code.name)))
        }
      })
  }
}
