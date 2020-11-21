/*  Title:      Pure/Thy/export.scala
    Author:     Makarius

Manage theory exports: compressed blobs.
*/

package isabelle


import scala.annotation.tailrec
import scala.util.matching.Regex


object Export
{
  /* name structure */

  def explode_name(s: String): List[String] = space_explode('/', s)
  def implode_name(elems: Iterable[String]): String = elems.mkString("/")


  /* SQL data model */

  object Data
  {
    val session_name = SQL.Column.string("session_name").make_primary_key
    val theory_name = SQL.Column.string("theory_name").make_primary_key
    val name = SQL.Column.string("name").make_primary_key
    val executable = SQL.Column.bool("executable")
    val compressed = SQL.Column.bool("compressed")
    val body = SQL.Column.bytes("body")

    val table =
      SQL.Table("isabelle_exports",
        List(session_name, theory_name, name, executable, compressed, body))

    def where_equal(session_name: String, theory_name: String = "", name: String = ""): SQL.Source =
      "WHERE " + Data.session_name.equal(session_name) +
        (if (theory_name == "") "" else " AND " + Data.theory_name.equal(theory_name)) +
        (if (name == "") "" else " AND " + Data.name.equal(name))
  }

  def read_name(db: SQL.Database, session_name: String, theory_name: String, name: String): Boolean =
  {
    val select =
      Data.table.select(List(Data.name), Data.where_equal(session_name, theory_name, name))
    db.using_statement(select)(stmt => stmt.execute_query().next())
  }

  def read_names(db: SQL.Database, session_name: String, theory_name: String): List[String] =
  {
    val select = Data.table.select(List(Data.name), Data.where_equal(session_name, theory_name))
    db.using_statement(select)(stmt =>
      stmt.execute_query().iterator(res => res.string(Data.name)).toList)
  }

  def read_theory_names(db: SQL.Database, session_name: String): List[String] =
  {
    val select =
      Data.table.select(List(Data.theory_name), Data.where_equal(session_name), distinct = true)
    db.using_statement(select)(stmt =>
      stmt.execute_query().iterator(_.string(Data.theory_name)).toList)
  }

  def read_theory_exports(db: SQL.Database, session_name: String): List[(String, String)] =
  {
    val select = Data.table.select(List(Data.theory_name, Data.name), Data.where_equal(session_name))
    db.using_statement(select)(stmt =>
      stmt.execute_query().iterator(res =>
        (res.string(Data.theory_name), res.string(Data.name))).toList)
  }

  def message(msg: String, theory_name: String, name: String): String =
    msg + " " + quote(name) + " for theory " + quote(theory_name)

  def compound_name(a: String, b: String): String = a + ":" + b

  def empty_entry(session_name: String, theory_name: String, name: String): Entry =
    Entry(session_name, theory_name, name, false, Future.value(false, Bytes.empty))

  sealed case class Entry(
    session_name: String,
    theory_name: String,
    name: String,
    executable: Boolean,
    body: Future[(Boolean, Bytes)])
  {
    override def toString: String = name

    def compound_name: String = Export.compound_name(theory_name, name)

    val name_elems: List[String] = explode_name(name)

    def name_extends(elems: List[String]): Boolean =
      name_elems.startsWith(elems) && name_elems != elems

    def text: String = uncompressed().text

    def uncompressed(cache: XZ.Cache = XZ.cache()): Bytes =
    {
      val (compressed, bytes) = body.join
      if (compressed) bytes.uncompress(cache = cache) else bytes
    }

    def uncompressed_yxml(cache: XZ.Cache = XZ.cache()): XML.Body =
      YXML.parse_body(UTF8.decode_permissive(uncompressed(cache = cache)))

    def write(db: SQL.Database)
    {
      val (compressed, bytes) = body.join
      db.using_statement(Data.table.insert())(stmt =>
      {
        stmt.string(1) = session_name
        stmt.string(2) = theory_name
        stmt.string(3) = name
        stmt.bool(4) = executable
        stmt.bool(5) = compressed
        stmt.bytes(6) = bytes
        stmt.execute()
      })
    }
  }

  def make_regex(pattern: String): Regex =
  {
    @tailrec def make(result: List[String], depth: Int, chs: List[Char]): Regex =
      chs match {
        case '*' :: '*' :: rest => make("[^:]*" :: result, depth, rest)
        case '*' :: rest => make("[^:/]*" :: result, depth, rest)
        case '?' :: rest => make("[^:/]" :: result, depth, rest)
        case '\\' :: c :: rest => make(("\\" + c) :: result, depth, rest)
        case '{' :: rest => make("(" :: result, depth + 1, rest)
        case ',' :: rest if depth > 0 => make("|" :: result, depth, rest)
        case '}' :: rest if depth > 0 => make(")" :: result, depth - 1, rest)
        case c :: rest if ".+()".contains(c) => make(("\\" + c) :: result, depth, rest)
        case c :: rest => make(c.toString :: result, depth, rest)
        case Nil => result.reverse.mkString.r
      }
    make(Nil, 0, pattern.toList)
  }

  def make_matcher(pattern: String): (String, String) => Boolean =
  {
    val regex = make_regex(pattern)
    (theory_name: String, name: String) =>
      regex.pattern.matcher(compound_name(theory_name, name)).matches
  }

  def make_entry(session_name: String, args: Protocol.Export.Args, body: Bytes,
    cache: XZ.Cache = XZ.cache()): Entry =
  {
    Entry(session_name, args.theory_name, args.name, args.executable,
      if (args.compress) Future.fork(body.maybe_compress(cache = cache))
      else Future.value((false, body)))
  }

  def read_entry(db: SQL.Database, session_name: String, theory_name: String, name: String)
    : Option[Entry] =
  {
    val select =
      Data.table.select(List(Data.executable, Data.compressed, Data.body),
        Data.where_equal(session_name, theory_name, name))
    db.using_statement(select)(stmt =>
    {
      val res = stmt.execute_query()
      if (res.next()) {
        val executable = res.bool(Data.executable)
        val compressed = res.bool(Data.compressed)
        val body = res.bytes(Data.body)
        Some(Entry(session_name, theory_name, name, executable, Future.value(compressed, body)))
      }
      else None
    })
  }

  def read_entry(dir: Path, session_name: String, theory_name: String, name: String): Option[Entry] =
  {
    val path = dir + Path.basic(theory_name) + Path.explode(name)
    if (path.is_file) {
      val executable = File.is_executable(path)
      val uncompressed = Bytes.read(path)
      Some(Entry(session_name, theory_name, name, executable, Future.value((false, uncompressed))))
    }
    else None
  }


  /* database consumer thread */

  def consumer(db: SQL.Database, cache: XZ.Cache = XZ.cache()): Consumer = new Consumer(db, cache)

  class Consumer private[Export](db: SQL.Database, cache: XZ.Cache)
  {
    private val errors = Synchronized[List[String]](Nil)

    private val consumer =
      Consumer_Thread.fork_bulk[(Entry, Boolean)](name = "export")(
        bulk = { case (entry, _) => entry.body.is_finished },
        consume =
          (args: List[(Entry, Boolean)]) =>
          {
            val results =
              db.transaction {
                for ((entry, strict) <- args)
                yield {
                  if (read_name(db, entry.session_name, entry.theory_name, entry.name)) {
                    if (strict) {
                      val msg = message("Duplicate export", entry.theory_name, entry.name)
                      errors.change(msg :: _)
                    }
                    Exn.Res(())
                  }
                  else Exn.capture { entry.write(db) }
                }
              }
            (results, true)
          })

    def apply(session_name: String, args: Protocol.Export.Args, body: Bytes): Unit =
      consumer.send(make_entry(session_name, args, body, cache = cache) -> args.strict)

    def shutdown(close: Boolean = false): List[String] =
    {
      consumer.shutdown()
      if (close) db.close()
      errors.value.reverse
    }
  }


  /* abstract provider */

  object Provider
  {
    def none: Provider =
      new Provider {
        def apply(export_name: String): Option[Entry] = None
        def focus(other_theory: String): Provider = this

        override def toString: String = "none"
      }

    def database_context(
        context: Sessions.Database_Context, session: String, theory_name: String): Provider =
      new Provider {
        def apply(export_name: String): Option[Entry] =
          context.try_export(session, theory_name, export_name)

        def focus(other_theory: String): Provider = this

        override def toString: String = context.toString
      }

    def database(db: SQL.Database, session_name: String, theory_name: String): Provider =
      new Provider {
        def apply(export_name: String): Option[Entry] =
          read_entry(db, session_name, theory_name, export_name)

        def focus(other_theory: String): Provider =
          if (other_theory == theory_name) this
          else Provider.database(db, session_name, other_theory)

        override def toString: String = db.toString
      }

    def snapshot(snapshot: Document.Snapshot): Provider =
      new Provider {
        def apply(export_name: String): Option[Entry] =
          snapshot.exports_map.get(export_name)

        def focus(other_theory: String): Provider =
          if (other_theory == snapshot.node_name.theory) this
          else {
            val node_name =
              snapshot.version.nodes.theory_name(other_theory) getOrElse
                error("Bad theory " + quote(other_theory))
            Provider.snapshot(snapshot.state.snapshot(node_name))
          }

        override def toString: String = snapshot.toString
      }

    def directory(dir: Path, session_name: String, theory_name: String): Provider =
      new Provider {
        def apply(export_name: String): Option[Entry] =
          read_entry(dir, session_name, theory_name, export_name)

        def focus(other_theory: String): Provider =
          if (other_theory == theory_name) this
          else Provider.directory(dir, session_name, other_theory)

        override def toString: String = dir.toString
      }
  }

  trait Provider
  {
    def apply(export_name: String): Option[Entry]

    def uncompressed_yxml(export_name: String, cache: XZ.Cache = XZ.cache()): XML.Body =
      apply(export_name) match {
        case Some(entry) => entry.uncompressed_yxml(cache = cache)
        case None => Nil
      }

    def focus(other_theory: String): Provider
  }


  /* export to file-system */

  def export_files(
    store: Sessions.Store,
    session_name: String,
    export_dir: Path,
    progress: Progress = new Progress,
    export_prune: Int = 0,
    export_list: Boolean = false,
    export_patterns: List[String] = Nil)
  {
    using(store.open_database(session_name))(db =>
    {
      db.transaction {
        val export_names = read_theory_exports(db, session_name)

        // list
        if (export_list) {
          (for ((theory_name, name) <- export_names) yield compound_name(theory_name, name)).
            sorted.foreach(progress.echo)
        }

        // export
        if (export_patterns.nonEmpty) {
          val exports =
            (for {
              export_pattern <- export_patterns.iterator
              matcher = make_matcher(export_pattern)
              (theory_name, name) <- export_names if matcher(theory_name, name)
            } yield (theory_name, name)).toSet
          for {
            (theory_name, group) <- exports.toList.groupBy(_._1).toList.sortBy(_._1)
            name <- group.map(_._2).sorted
            entry <- read_entry(db, session_name, theory_name, name)
          } {
            val elems = theory_name :: space_explode('/', name)
            val path =
              if (elems.length < export_prune + 1) {
                error("Cannot prune path by " + export_prune + " element(s): " + Path.make(elems))
              }
              else export_dir + Path.make(elems.drop(export_prune))

            progress.echo("export " + path + (if (entry.executable) " (executable)" else ""))
            Isabelle_System.make_directory(path.dir)
            Bytes.write(path, entry.uncompressed(cache = store.xz_cache))
            File.set_executable(path, entry.executable)
          }
        }
      }
    })
  }


  /* Isabelle tool wrapper */

  val default_export_dir: Path = Path.explode("export")

  val isabelle_tool = Isabelle_Tool("export", "retrieve theory exports", args =>
  {
    /* arguments */

    var export_dir = default_export_dir
    var dirs: List[Path] = Nil
    var export_list = false
    var no_build = false
    var options = Options.init()
    var export_prune = 0
    var export_patterns: List[String] = Nil

    val getopts = Getopts("""
Usage: isabelle export [OPTIONS] SESSION

  Options are:
    -O DIR       output directory for exported files (default: """ + default_export_dir + """)
    -d DIR       include session directory
    -l           list exports
    -n           no build of session
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -p NUM       prune path of exported files by NUM elements
    -x PATTERN   extract files matching pattern (e.g. "*:**" for all)

  List or export theory exports for SESSION: named blobs produced by
  isabelle build. Option -l or -x is required; option -x may be repeated.

  The PATTERN language resembles glob patterns in the shell, with ? and *
  (both excluding ":" and "/"), ** (excluding ":"), and [abc] or [^abc],
  and variants {pattern1,pattern2,pattern3}.
""",
      "O:" -> (arg => export_dir = Path.explode(arg)),
      "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
      "l" -> (_ => export_list = true),
      "n" -> (_ => no_build = true),
      "o:" -> (arg => options = options + arg),
      "p:" -> (arg => export_prune = Value.Int.parse(arg)),
      "x:" -> (arg => export_patterns ::= arg))

    val more_args = getopts(args)
    val session_name =
      more_args match {
        case List(session_name) if export_list || export_patterns.nonEmpty => session_name
        case _ => getopts.usage()
      }

    val progress = new Console_Progress()


    /* build */

    if (!no_build) {
      val rc =
        progress.interrupt_handler {
          Build.build_logic(options, session_name, progress = progress, dirs = dirs)
        }
      if (rc != 0) sys.exit(rc)
    }


    /* export files */

    val store = Sessions.store(options)
    export_files(store, session_name, export_dir, progress = progress, export_prune = export_prune,
      export_list = export_list, export_patterns = export_patterns)
  })
}
