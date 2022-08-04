/*  Title:      Pure/Thy/export.scala
    Author:     Makarius

Manage theory exports: compressed blobs.
*/

package isabelle


import scala.annotation.tailrec
import scala.util.matching.Regex


object Export {
  /* artefact names */

  val DOCUMENT_ID = "PIDE/document_id"
  val FILES = "PIDE/files"
  val MARKUP = "PIDE/markup"
  val MESSAGES = "PIDE/messages"
  val DOCUMENT_PREFIX = "document/"
  val DOCUMENT_LATEX = DOCUMENT_PREFIX + "latex"
  val DOCUMENT_CITATIONS = DOCUMENT_PREFIX + "citations"
  val THEORY_PREFIX: String = "theory/"
  val PROOFS_PREFIX: String = "proofs/"

  def explode_name(s: String): List[String] = space_explode('/', s)
  def implode_name(elems: Iterable[String]): String = elems.mkString("/")


  /* SQL data model */

  object Data {
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

  def compound_name(a: String, b: String): String =
    if (a.isEmpty) b else a + ":" + b

  sealed case class Entry_Name(session: String = "", theory: String = "", name: String = "") {
    val compound_name: String = Export.compound_name(theory, name)

    def make_path(prune: Int = 0): Path = {
      val elems = theory :: space_explode('/', name)
      if (elems.length < prune + 1) {
        error("Cannot prune path by " + prune + " element(s): " + Path.make(elems))
      }
      else Path.make(elems.drop(prune))
    }

    def readable(db: SQL.Database): Boolean = {
      val select = Data.table.select(List(Data.name), Data.where_equal(session, theory, name))
      db.using_statement(select)(stmt => stmt.execute_query().next())
    }

    def read(db: SQL.Database, cache: XML.Cache): Option[Entry] = {
      val select =
        Data.table.select(List(Data.executable, Data.compressed, Data.body),
          Data.where_equal(session, theory, name))
      db.using_statement(select) { stmt =>
        val res = stmt.execute_query()
        if (res.next()) {
          val executable = res.bool(Data.executable)
          val compressed = res.bool(Data.compressed)
          val bytes = res.bytes(Data.body)
          val body = Future.value(compressed, bytes)
          Some(Entry(this, executable, body, cache))
        }
        else None
      }
    }
  }

  def read_theory_names(db: SQL.Database, session_name: String): List[String] = {
    val select =
      Data.table.select(List(Data.theory_name), Data.where_equal(session_name), distinct = true)
    db.using_statement(select)(stmt =>
      stmt.execute_query().iterator(_.string(Data.theory_name)).toList)
  }

  def read_entry_names(db: SQL.Database, session_name: String): List[Entry_Name] = {
    val select =
      Data.table.select(List(Data.theory_name, Data.name), Data.where_equal(session_name)) +
      " ORDER BY " + Data.theory_name + ", " + Data.name
    db.using_statement(select)(stmt =>
      stmt.execute_query().iterator(res =>
        Entry_Name(session = session_name,
          theory = res.string(Data.theory_name),
          name = res.string(Data.name))).toList)
  }

  def message(msg: String, theory_name: String, name: String): String =
    msg + " " + quote(name) + " for theory " + quote(theory_name)

  def empty_entry(theory_name: String, name: String): Entry =
    Entry(Entry_Name(theory = theory_name, name = name),
      false, Future.value(false, Bytes.empty), XML.Cache.none)

  sealed case class Entry(
    entry_name: Entry_Name,
    executable: Boolean,
    body: Future[(Boolean, Bytes)],
    cache: XML.Cache
  ) {
    def session_name: String = entry_name.session
    def theory_name: String = entry_name.theory
    def name: String = entry_name.name
    override def toString: String = name

    def compound_name: String = entry_name.compound_name

    def name_has_prefix(s: String): Boolean = name.startsWith(s)
    val name_elems: List[String] = explode_name(name)

    def name_extends(elems: List[String]): Boolean =
      name_elems.startsWith(elems) && name_elems != elems

    def text: String = uncompressed.text

    def uncompressed: Bytes = {
      val (compressed, bytes) = body.join
      if (compressed) bytes.uncompress(cache = cache.xz) else bytes
    }

    def uncompressed_yxml: XML.Body =
      YXML.parse_body(UTF8.decode_permissive(uncompressed), cache = cache)

    def write(db: SQL.Database): Unit = {
      val (compressed, bytes) = body.join
      db.using_statement(Data.table.insert()) { stmt =>
        stmt.string(1) = session_name
        stmt.string(2) = theory_name
        stmt.string(3) = name
        stmt.bool(4) = executable
        stmt.bool(5) = compressed
        stmt.bytes(6) = bytes
        stmt.execute()
      }
    }
  }

  def make_regex(pattern: String): Regex = {
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

  def make_matcher(pats: List[String]): Entry_Name => Boolean = {
    val regs = pats.map(make_regex)
    (entry_name: Entry_Name) =>
      regs.exists(_.pattern.matcher(entry_name.compound_name).matches)
  }

  def make_entry(
    session_name: String,
    args: Protocol.Export.Args,
    bytes: Bytes,
    cache: XML.Cache
  ): Entry = {
    val body =
      if (args.compress) Future.fork(bytes.maybe_compress(cache = cache.xz))
      else Future.value((false, bytes))
    val entry_name = Entry_Name(session = session_name, theory = args.theory_name, name = args.name)
    Entry(entry_name, args.executable, body, cache)
  }


  /* specific entries */

  def read_document_id(read: String => Entry): Option[Long] =
    read(DOCUMENT_ID).text match {
      case Value.Long(id) => Some(id)
      case _ => None
    }

  def read_files(read: String => Entry): Option[(String, List[String])] =
    split_lines(read(FILES).text) match {
      case thy_file :: blobs_files => Some((thy_file, blobs_files))
      case Nil => None
    }


  /* database consumer thread */

  def consumer(db: SQL.Database, cache: XML.Cache, progress: Progress = new Progress): Consumer =
    new Consumer(db, cache, progress)

  class Consumer private[Export](db: SQL.Database, cache: XML.Cache, progress: Progress) {
    private val errors = Synchronized[List[String]](Nil)

    private val consumer =
      Consumer_Thread.fork_bulk[(Entry, Boolean)](name = "export")(
        bulk = { case (entry, _) => entry.body.is_finished },
        consume =
          { (args: List[(Entry, Boolean)]) =>
            val results =
              db.transaction {
                for ((entry, strict) <- args)
                yield {
                  if (progress.stopped) {
                    entry.body.cancel()
                    Exn.Res(())
                  }
                  else if (entry.entry_name.readable(db)) {
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

    def apply(session_name: String, args: Protocol.Export.Args, body: Bytes): Unit = {
      if (!progress.stopped) {
        consumer.send(make_entry(session_name, args, body, cache) -> args.strict)
      }
    }

    def shutdown(close: Boolean = false): List[String] = {
      consumer.shutdown()
      if (close) db.close()
      errors.value.reverse ::: (if (progress.stopped) List("Export stopped") else Nil)
    }
  }


  /* abstract provider */

  object Provider {
    private def database_provider(
        db: SQL.Database,
        cache: XML.Cache,
        session: String,
        theory: String,
        _theory_names: Synchronized[Option[List[String]]]
    ): Provider = {
      new Provider {
        override def theory_names: List[String] =
          _theory_names.change_result { st =>
            val res = st.getOrElse(read_theory_names(db, session))
            (res, Some(res))
          }

        override def apply(export_name: String): Option[Entry] =
          if (theory.isEmpty) None
          else {
            Entry_Name(session = session, theory = theory, name = export_name)
              .read(db, cache)
          }

        override def focus(other_theory: String): Provider =
          if (other_theory == theory) this
          else database_provider(db, cache, session, theory, _theory_names)

        override def toString: String = db.toString
      }
    }

    def database(
      db: SQL.Database,
      cache: XML.Cache,
      session: String,
      theory: String = ""
    ): Provider = database_provider(db, cache, session, theory, Synchronized(None))

    def snapshot(
      resources: Resources,
      snapshot: Document.Snapshot
    ): Provider =
      new Provider {
        override def theory_names: List[String] =
          (for {
            (name, _) <- snapshot.version.nodes.iterator
            if name.is_theory && !resources.session_base.loaded_theory(name)
          } yield name.theory).toList

        override def apply(export_name: String): Option[Entry] =
          snapshot.exports_map.get(export_name)

        override def focus(other_theory: String): Provider =
          if (other_theory == snapshot.node_name.theory) this
          else {
            val node_name =
              snapshot.version.nodes.theory_name(other_theory) getOrElse
                error("Bad theory " + quote(other_theory))
            Provider.snapshot(resources, snapshot.state.snapshot(node_name))
          }

        override def toString: String = snapshot.toString
      }
  }

  trait Provider {
    def theory_names: List[String]

    def apply(export_name: String): Option[Entry]

    def uncompressed_yxml(export_name: String): XML.Body =
      apply(export_name) match {
        case Some(entry) => entry.uncompressed_yxml
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
    export_patterns: List[String] = Nil
  ): Unit = {
    using(store.open_database(session_name)) { db =>
      val entry_names = read_entry_names(db, session_name)

      // list
      if (export_list) {
        for (entry_name <- entry_names) progress.echo(entry_name.compound_name)
      }

      // export
      if (export_patterns.nonEmpty) {
        val matcher = make_matcher(export_patterns)
        for {
          entry_name <- entry_names if matcher(entry_name)
          entry <- entry_name.read(db, store.cache)
        } {
          val path = export_dir + entry_name.make_path(prune = export_prune)
          progress.echo("export " + path + (if (entry.executable) " (executable)" else ""))
          Isabelle_System.make_directory(path.dir)
          val bytes = entry.uncompressed
          if (!path.is_file || Bytes.read(path) != bytes) Bytes.write(path, bytes)
          File.set_executable(path, entry.executable)
        }
      }
    }
  }


  /* Isabelle tool wrapper */

  val default_export_dir: Path = Path.explode("export")

  val isabelle_tool =
    Isabelle_Tool("export", "retrieve theory exports", Scala_Project.here,
      { args =>
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
          if (rc != Process_Result.RC.ok) sys.exit(rc)
        }


        /* export files */

        val store = Sessions.store(options)
        export_files(store, session_name, export_dir, progress = progress, export_prune = export_prune,
          export_list = export_list, export_patterns = export_patterns)
      })
}
