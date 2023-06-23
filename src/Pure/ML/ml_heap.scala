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

      val table = make_table("", List(name, size, digest))
    }

    object Slices {
      val name = Generic.name
      val slice = SQL.Column.int("slice").make_primary_key
      val content = SQL.Column.bytes("content")

      val table = make_table("slices", List(name, slice, content))
    }

    def known_entry(db: SQL.Database, name: String): Boolean =
      db.execute_query_statementB(
        Base.table.select(List(Base.name), sql = Base.name.where_equal(name)))

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

  def clean_entry(db: SQL.Database, name: String): Unit =
    Data.transaction_lock(db, create = true) { Data.clean_entry(db, name) }

  def get_entry(db: SQL.Database, name: String): Option[SHA1.Digest] =
    Data.transaction_lock(db, create = true) { Data.get_entry(db, name) }

  def store(
    database: Option[SQL.Database],
    heap: Path,
    slice: Long,
    cache: Compress.Cache = Compress.Cache.none
  ): SHA1.Digest = {
    val digest = write_file_digest(heap)
    database match {
      case Some(db) =>
        val name = heap.file_name
        val size = File.space(heap).bytes - sha1_prefix.length - SHA1.digest_length

        val slices = (size.toDouble / slice.toDouble).ceil.toInt
        val step = (size.toDouble / slices.toDouble).ceil.toLong

        try {
          Data.transaction_lock(db, create = true) { Data.prepare_entry(db, name) }

          for (i <- 0 until slices) {
            val j = i + 1
            val offset = step * i
            val limit = if (j < slices) step * j else size
            val content =
              Bytes.read_file(heap.file, offset = offset, limit = limit)
                .compress(cache = cache)
            Data.transaction_lock(db) { Data.write_entry(db, name, i, content) }
          }

          Data.transaction_lock(db) { Data.finish_entry(db, name, size, digest) }
        }
        catch { case exn: Throwable =>
          Data.transaction_lock(db, create = true) { Data.clean_entry(db, name) }
          throw exn
        }
      case None =>
    }
    digest
  }

  def restore(
    db: SQL.Database,
    heap: Path,
    cache: Compress.Cache = Compress.Cache.none
  ): Unit = {
    val name = heap.file_name
    Data.transaction_lock(db, create = true) {
      val db_digest = Data.get_entry(db, name)
      val file_digest = read_file_digest(heap)

      if (db_digest.isDefined && db_digest != file_digest) {
        Isabelle_System.make_directory(heap.expand.dir)
        Bytes.write(heap, Bytes.empty)
          for (slice <- Data.read_entry(db, name)) {
            Bytes.append(heap, slice.uncompress(cache = cache))
          }
        val digest = write_file_digest(heap)
        if (db_digest.get != digest) error("Incoherent content for file " + heap)
      }
    }
  }
}
