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
      val n = File.size(heap)
      val bs = Bytes.read_file(heap, offset = n - m)
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

  object private_data extends SQL.Data("isabelle_heaps") {
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

    def get_entries(db: SQL.Database, names: Iterable[String]): Map[String, SHA1.Digest] = {
      require(names.nonEmpty)

      db.execute_query_statement(
        Base.table.select(List(Base.name, Base.digest),
          sql = Generic.name.where_member(names)),
        List.from[(String, String)],
        res => res.string(Base.name) -> res.string(Base.digest)
      ).flatMap({
        case (_, "") => None
        case (name, digest) => Some(name -> SHA1.fake_digest(digest))
      }).toMap
    }

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
    private_data.transaction_lock(db, create = true, label = "ML_Heap.clean_entry") {
      private_data.clean_entry(db, session_name)
    }

  def get_entries(db: SQL.Database, names: Iterable[String]): Map[String, SHA1.Digest] =
    private_data.transaction_lock(db, create = true, label = "ML_Heap.get_entries") {
      private_data.get_entries(db, names)
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
        val size = File.size(heap) - sha1_prefix.length - SHA1.digest_length

        val slices = (size.toDouble / slice.toDouble).ceil.toInt
        val step = (size.toDouble / slices.toDouble).ceil.toLong

        try {
          private_data.transaction_lock(db, create = true, label = "ML_Heap.store1") {
            private_data.prepare_entry(db, session_name)
          }

          for (i <- 0 until slices) {
            val j = i + 1
            val offset = step * i
            val limit = if (j < slices) step * j else size
            val content =
              Bytes.read_file(heap, offset = offset, limit = limit)
                .compress(cache = cache)
            private_data.transaction_lock(db, label = "ML_Heap.store2") {
              private_data.write_entry(db, session_name, i, content)
            }
          }

          private_data.transaction_lock(db, label = "ML_Heap.store3") {
            private_data.finish_entry(db, session_name, size, digest)
          }
        }
        catch { case exn: Throwable =>
          private_data.transaction_lock(db, create = true, label = "ML_Heap.store4") {
            private_data.clean_entry(db, session_name)
          }
          throw exn
        }
    }
    digest
  }

  def restore(
    database: Option[SQL.Database],
    heaps: List[Path],
    cache: Compress.Cache = Compress.Cache.none
  ): Unit = {
    database match {
      case Some(db) if heaps.nonEmpty =>
        private_data.transaction_lock(db, create = true, label = "ML_Heap.restore") {
          val db_digests = private_data.get_entries(db, heaps.map(_.file_name))
          for (heap <- heaps) {
            val session_name = heap.file_name
            val file_digest = read_file_digest(heap)
            val db_digest = db_digests.get(session_name)
            if (db_digest.isDefined && db_digest != file_digest) {
              val base_dir = Isabelle_System.make_directory(heap.expand.dir)
              Isabelle_System.with_tmp_file(session_name + "_", base_dir = base_dir.file) { tmp =>
                Bytes.write(tmp, Bytes.empty)
                for (slice <- private_data.read_entry(db, session_name)) {
                  Bytes.append(tmp, slice.uncompress(cache = cache))
                }
                val digest = write_file_digest(tmp)
                if (db_digest.get == digest) {
                  Isabelle_System.chmod("a+r", tmp)
                  Isabelle_System.move_file(tmp, heap)
                }
                else error("Incoherent content for session heap " + quote(session_name))
              }
            }
          }
        }
      case _ =>
    }
  }
}
