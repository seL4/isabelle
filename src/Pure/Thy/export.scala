/*  Title:      Pure/Thy/export.scala
    Author:     Makarius

Manage theory exports: compressed blobs.
*/

package isabelle


import scala.annotation.tailrec
import scala.util.matching.Regex


object Export
{
  /* SQL data model */

  object Data
  {
    val session_name = SQL.Column.string("session_name").make_primary_key
    val theory_name = SQL.Column.string("theory_name").make_primary_key
    val name = SQL.Column.string("name").make_primary_key
    val compressed = SQL.Column.bool("compressed")
    val body = SQL.Column.bytes("body")

    val table =
      SQL.Table("isabelle_exports", List(session_name, theory_name, name, compressed, body))

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

  def read_theory_names(db: SQL.Database, session_name: String): List[(String, String)] =
  {
    val select = Data.table.select(List(Data.theory_name, Data.name), Data.where_equal(session_name))
    db.using_statement(select)(stmt =>
      stmt.execute_query().iterator(res =>
        (res.string(Data.theory_name), res.string(Data.name))).toList)
  }

  def message(msg: String, theory_name: String, name: String): String =
    msg + " " + quote(name) + " for theory " + quote(theory_name)

  def compound_name(a: String, b: String): String = a + ":" + b

  sealed case class Entry(
    session_name: String,
    theory_name: String,
    name: String,
    body: Future[(Boolean, Bytes)])
  {
    override def toString: String = compound_name(theory_name, name)

    def write(db: SQL.Database)
    {
      val (compressed, bytes) = body.join
      db.using_statement(Data.table.insert())(stmt =>
      {
        stmt.string(1) = session_name
        stmt.string(2) = theory_name
        stmt.string(3) = name
        stmt.bool(4) = compressed
        stmt.bytes(5) = bytes
        stmt.execute()
      })
    }

    def uncompressed(cache: XZ.Cache = XZ.cache()): Bytes =
    {
      val (compressed, bytes) = body.join
      if (compressed) bytes.uncompress(cache = cache) else bytes
    }

    def uncompressed_yxml(cache: XZ.Cache = XZ.cache()): XML.Body =
      YXML.parse_body(UTF8.decode_permissive(uncompressed(cache = cache)))
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

  def make_entry(session_name: String, args: Markup.Export.Args, body: Bytes,
    cache: XZ.Cache = XZ.cache()): Entry =
  {
    Entry(session_name, args.theory_name, args.name,
      if (args.compress) Future.fork(body.maybe_compress(cache = cache))
      else Future.value((false, body)))
  }

  def read_entry(db: SQL.Database, session_name: String, theory_name: String, name: String)
    : Option[Entry] =
  {
    val select =
      Data.table.select(List(Data.compressed, Data.body),
        Data.where_equal(session_name, theory_name, name))
    db.using_statement(select)(stmt =>
    {
      val res = stmt.execute_query()
      if (res.next()) {
        val compressed = res.bool(Data.compressed)
        val body = res.bytes(Data.body)
        Some(Entry(session_name, theory_name, name, Future.value(compressed, body)))
      }
      else None
    })
  }


  /* database consumer thread */

  def consumer(db: SQL.Database): Consumer = new Consumer(db)

  class Consumer private[Export](db: SQL.Database)
  {
    val xz_cache = XZ.make_cache()

    db.create_table(Data.table)

    private val export_errors = Synchronized[List[String]](Nil)

    private val consumer =
      Consumer_Thread.fork(name = "export")(consume = (entry: Entry) =>
        {
          entry.body.join
          db.transaction {
            if (read_name(db, entry.session_name, entry.theory_name, entry.name)) {
              val err = message("Duplicate export", entry.theory_name, entry.name)
              export_errors.change(errs => err :: errs)
            }
            else entry.write(db)
          }
          true
        })

    def apply(session_name: String, args: Markup.Export.Args, body: Bytes): Unit =
      consumer.send(make_entry(session_name, args, body, cache = xz_cache))

    def shutdown(close: Boolean = false): List[String] =
    {
      consumer.shutdown()
      if (close) db.close()
      export_errors.value.reverse
    }
  }


  /* Isabelle tool wrapper */

  val default_export_dir = Path.explode("export")

  val isabelle_tool = Isabelle_Tool("export", "retrieve theory exports", args =>
  {
    /* arguments */

    var export_dir = default_export_dir
    var dirs: List[Path] = Nil
    var export_list = false
    var no_build = false
    var options = Options.init()
    var system_mode = false
    var export_pattern = ""

    val getopts = Getopts("""
Usage: isabelle export [OPTIONS] SESSION

  Options are:
    -D DIR       target directory for exported files (default: """ + default_export_dir + """)
    -d DIR       include session directory
    -l           list exports
    -n           no build of session
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -s           system build mode for session image
    -x PATTERN   extract files matching pattern (e.g. "*:**" for all)

  List or export theory exports for SESSION: named blobs produced by
  isabelle build. Option -l or -x is required.

  The PATTERN language resembles glob patterns in the shell, with ? and *
  (both excluding ":" and "/"), ** (excluding ":"), and [abc] or [^abc],
  and variants {pattern1,pattern2,pattern3}.
""",
      "D:" -> (arg => export_dir = Path.explode(arg)),
      "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
      "l" -> (_ => export_list = true),
      "n" -> (_ => no_build = true),
      "o:" -> (arg => options = options + arg),
      "s" -> (_ => system_mode = true),
      "x:" -> (arg => export_pattern = arg))

    val more_args = getopts(args)
    val session_name =
      more_args match {
        case List(session_name) if export_list || export_pattern != "" => session_name
        case _ => getopts.usage()
      }


    /* build */

    val progress = new Console_Progress()

    if (!no_build &&
        !Build.build(options, no_build = true, dirs = dirs, system_mode = system_mode,
          sessions = List(session_name)).ok)
    {
      progress.echo("Build started for Isabelle/" + session_name + " ...")
      progress.interrupt_handler {
        val res =
          Build.build(options, progress = progress, dirs = dirs, system_mode = system_mode,
            sessions = List(session_name))
        if (!res.ok) sys.exit(res.rc)
      }
    }


    /* database */

    val store = Sessions.store(system_mode)

    using(SQLite.open_database(store.the_database(session_name)))(db =>
    {
      db.transaction {
        val export_names = read_theory_names(db, session_name)

        // list
        if (export_list) {
          (for ((theory_name, name) <- export_names) yield compound_name(theory_name, name)).
            sorted.foreach(Output.writeln(_, stdout = true))
        }

        // export
        if (export_pattern != "") {
          val xz_cache = XZ.make_cache()

          val matcher = make_matcher(export_pattern)
          for {
            (theory_name, name) <- export_names if matcher(theory_name, name)
            entry <- read_entry(db, session_name, theory_name, name)
          } {
            val path = export_dir + Path.basic(theory_name) + Path.explode(name)
            progress.echo("exporting " + path)
            Isabelle_System.mkdirs(path.dir)
            Bytes.write(path, entry.uncompressed(cache = xz_cache))
          }
        }
      }
    })
  })
}
