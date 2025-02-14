/*  Title:      Pure/General/file_store.scala
    Author:     Makarius

Persistent store for file-system content, backed by SQL database
(notably SQLite).
*/

package isabelle


import java.io.{File => JFile}


object File_Store {
  /* main operations */

  def make_database(database: Path, dir: Path,
    pred: JFile => Boolean = _ => true,
    name_prefix: String = "",
    compress_options: Compress.Options = Compress.Options(),
    compress_cache: Compress.Cache = Compress.Cache.none
  ): Unit = {
    database.file.delete()
    using(SQLite.open_database(database)) { db =>
      private_data.transaction_lock(db, create = true) {
        val root = dir.canonical_file
        val root_path = File.path(root)
        for {
          file <- File.find_files(root, pred = pred)
          rel_path <- File.relative_path(root_path, File.path(file))
        } {
          val entry =
            Entry.read_file(rel_path, name_prefix = name_prefix, dir = root_path,
              compress_options = compress_options, compress_cache = compress_cache)
          private_data.write_entry(db, entry)
        }
      }
    }
  }

  def database_entry(database: Path, name: String): Option[Entry] =
    if (database.is_file) {
      using(SQLite.open_database(database)) { db =>
        private_data.transaction_lock(db) {
          if (private_data.tables_ok(db)) private_data.read_entry(db, name)
          else None
        }
      }
    }
    else None

  def database_extract(database: Path, dir: Path,
    compress_cache: Compress.Cache = Compress.Cache.none
  ): Unit = {
    if (database.is_file) {
      using(SQLite.open_database(database)) { db =>
        private_data.transaction_lock(db) {
          if (private_data.tables_ok(db)) {
            for {
              name <- private_data.read_names(db)
              entry <- private_data.read_entry(db, name)
            } entry.write_file(dir, compress_cache = compress_cache)
          }
        }
      }
    }
  }


  /* entry */

  object Entry {
    def read_file(path: Path,
      name_prefix: String = "",
      dir: Path = Path.current,
      compress_options: Compress.Options = Compress.Options(),
      compress_cache: Compress.Cache = Compress.Cache.none
    ): Entry = {
      val name = Url.append_path(name_prefix, path.expand.implode)
      val bs = Bytes.read(dir + path)
      val size = bs.size
      val digest = SHA1.digest(bs).toString
      val executable = File.is_executable(dir + path)
      val (compressed, body) = bs.maybe_compress(options = compress_options, cache = compress_cache)
      Entry(name, size, digest, executable, compressed, body)
    }
  }

  sealed case class Entry(
    name: String,
    size: Long,
    digest: String,
    executable: Boolean,
    compressed: Boolean,
    body: Bytes
  ) {
    require(name.nonEmpty && size >= 0 && (size > 0 || !compressed))

    def content(compress_cache: Compress.Cache = Compress.Cache.none): Bytes =
      if (compressed) body.uncompress(cache = compress_cache) else body

    def write_file(dir: Path, compress_cache: Compress.Cache = Compress.Cache.none): Unit = {
      val path = Path.explode(name)
      File.content(path, content(compress_cache = compress_cache)).write(dir)
      if (executable) File.set_executable(dir + path)
    }
  }


  /* SQL data model */

  object private_data extends SQL.Data() {
    override lazy val tables: SQL.Tables = SQL.Tables(Base.table)

    object Base {
      val name = SQL.Column.string("name").make_primary_key
      val size = SQL.Column.long("size")
      val digest = SQL.Column.string("digest")
      val executable = SQL.Column.bool("executable")
      val compressed = SQL.Column.bool("compressed")
      val body = SQL.Column.bytes("body")

      val table =
        SQL.Table("isabelle_file_store", List(name, size, digest, executable, compressed, body))
    }

    def read_names(db: SQL.Database): List[String] =
      db.execute_query_statement(
        Base.table.select(List(Base.name)),
        List.from[String], _.string(Base.name)
      ).sorted

    def read_entry(db: SQL.Database, name: String): Option[Entry] =
      db.execute_query_statementO[Entry](
        Base.table.select(Base.table.columns, sql = Base.name.where_equal(name)),
        { res =>
          val size = res.long(Base.size)
          val digest = proper_string(res.string(Base.digest)).getOrElse(SHA1.digest_empty.toString)
          val executable = res.bool(Base.executable)
          val compressed = res.bool(Base.compressed)
          val body = res.bytes(Base.body)
          Entry(name, size, digest, executable, compressed, body)
        })

    def write_entry(db: SQL.Database, entry: Entry): Unit =
      db.execute_statement(Base.table.insert(), body = { stmt =>
        stmt.string(1) = entry.name
        stmt.long(2) = entry.size
        stmt.string(3) = if (entry.digest == SHA1.digest_empty.toString) None else Some(entry.digest)
        stmt.bool(4) = entry.executable
        stmt.bool(5) = entry.compressed
        stmt.bytes(6) = entry.body
      })
  }
}
