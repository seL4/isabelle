/*  Title:      Pure/ML/ml_heap.scala
    Author:     Makarius

ML heap operations.
*/

package isabelle


import java.nio.ByteBuffer
import java.nio.channels.FileChannel
import java.nio.file.StandardOpenOption


object ML_Heap {
  /** heap file with SHA1 digest **/

  private val sha1_prefix = "SHA1:"

  def read_file_digest(heap: Path): Option[SHA1.Digest] = {
    if (heap.is_file) {
      val l = sha1_prefix.length
      val m = l + SHA1.digest_length
      val n = heap.file.length
      val bs = Bytes.read_file(heap.file, offset = n - m)
      if (bs.length == m) {
        val s = bs.text
        if (s.startsWith(sha1_prefix)) Some(SHA1.fake_digest(s.substring(l)))
        else None
      }
      else None
    }
    else None
  }

  def write_file_digest(heap: Path): SHA1.Digest =
    read_file_digest(heap) getOrElse {
      val digest = SHA1.digest(heap)
      File.append(heap, sha1_prefix + digest.toString)
      digest
    }


  /* SQL data model */

  object Data extends SQL.Data("isabelle_heaps") {
    override lazy val tables = SQL.Tables(Base.table, Slices.table)

    object Generic {
      val name = SQL.Column.string("name").make_primary_key
    }

    object Base {
      val name = Generic.name
      val size = SQL.Column.long("size")
      val digest = SQL.Column.string("digest")

      val table = make_table(List(name, size, digest))
    }

    object Slices {
      val name = Generic.name
      val slice = SQL.Column.int("slice").make_primary_key
      val content = SQL.Column.bytes("content")

      val table = make_table(List(name, slice, content), name = "slices")
    }

    object Slices_Size {
      val name = Generic.name
      val slice = SQL.Column.int("slice").make_primary_key
      val size = SQL.Column.long("size")

      val table = make_table(List(name, slice, size),
        body = "SELECT name, slice, pg_size_pretty(length(content)::bigint) as size FROM " +
          Slices.table.ident,
        name = "slices_size")
    }

    def get_entry(db: SQL.Database, name: String): Option[SHA1.Digest] =
      db.execute_query_statementO[String](
        Base.table.select(List(Base.digest), sql = Generic.name.where_equal(name)),
        _.string(Base.digest)
      ).flatMap(proper_string).map(SHA1.fake_digest)

    def read_entry(db: SQL.Database, name: String): List[Bytes] =
      db.execute_query_statement(
        Slices.table.select(List(Slices.content),
          sql = Generic.name.where_equal(name) + SQL.order_by(List(Slices.slice))),
        List.from[Bytes], _.bytes(Slices.content))

    def clean_entry(db: SQL.Database, name: String): Unit = {
      for (table <- List(Base.table, Slices.table)) {
        db.execute_statement(table.delete(sql = Base.name.where_equal(name)))
      }
      db.create_view(Slices_Size.table)
    }

    def prepare_entry(db: SQL.Database, name: String): Unit =
      db.execute_statement(Base.table.insert(), body =
        { stmt =>
          stmt.string(1) = name
          stmt.long(2) = None
          stmt.string(3) = None
        })

    def write_entry(db: SQL.Database, name: String, slice: Int, content: Bytes): Unit =
      db.execute_statement(Slices.table.insert(), body =
      { stmt =>
        stmt.string(1) = name
        stmt.int(2) = slice
        stmt.bytes(3) = content
      })

    def finish_entry(db: SQL.Database, name: String, size: Long, digest: SHA1.Digest): Unit =
      db.execute_statement(
        Base.table.update(List(Base.size, Base.digest), sql = Base.name.where_equal(name)),
        body =
          { stmt =>
            stmt.long(1) = size
            stmt.string(2) = digest.toString
          })
  }

  def clean_entry(db: SQL.Database, session_name: String): Unit =
    Data.transaction_lock(db, create = true, label = "ML_Heap.clean_entry") {
      Data.clean_entry(db, session_name)
    }

  def get_entry(db: SQL.Database, session_name: String): Option[SHA1.Digest] =
    Data.transaction_lock(db, create = true, label = "ML_Heap.get_entry") {
      Data.get_entry(db, session_name)
    }

  def store(
    database: Option[SQL.Database],
    session_name: String,
    heap: Path,
    slice: Long,
    cache: Compress.Cache = Compress.Cache.none
  ): SHA1.Digest = {
    val digest = write_file_digest(heap)
    database match {
      case None =>
      case Some(db) =>
        val size = File.space(heap).bytes - sha1_prefix.length - SHA1.digest_length

        val slices = (size.toDouble / slice.toDouble).ceil.toInt
        val step = (size.toDouble / slices.toDouble).ceil.toLong

        try {
          Data.transaction_lock(db, create = true, label = "ML_Heap.store1") {
            Data.prepare_entry(db, session_name)
          }

          for (i <- 0 until slices) {
            val j = i + 1
            val offset = step * i
            val limit = if (j < slices) step * j else size
            val content =
              Bytes.read_file(heap.file, offset = offset, limit = limit)
                .compress(cache = cache)
            Data.transaction_lock(db, label = "ML_Heap.store2") {
              Data.write_entry(db, session_name, i, content)
            }
          }

          Data.transaction_lock(db, label = "ML_Heap.store3") {
            Data.finish_entry(db, session_name, size, digest)
          }
        }
        catch { case exn: Throwable =>
          Data.transaction_lock(db, create = true, label = "ML_Heap.store4") {
            Data.clean_entry(db, session_name)
          }
          throw exn
        }
    }
    digest
  }

  def restore(
    database: Option[SQL.Database],
    session_name: String,
    heap: Path,
    cache: Compress.Cache = Compress.Cache.none
  ): Unit = {
    database match {
      case None =>
      case Some(db) =>
        Data.transaction_lock(db, create = true, label = "ML_Heap.restore") {
          val db_digest = Data.get_entry(db, session_name)
          val file_digest = read_file_digest(heap)

          if (db_digest.isDefined && db_digest != file_digest) {
            Isabelle_System.make_directory(heap.expand.dir)
            Bytes.write(heap, Bytes.empty)
              for (slice <- Data.read_entry(db, session_name)) {
                Bytes.append(heap, slice.uncompress(cache = cache))
              }
            val digest = write_file_digest(heap)
            if (db_digest.get != digest) error("Incoherent content for file " + heap)
          }
        }
    }
  }
}
