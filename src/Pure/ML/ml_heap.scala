/*  Title:      Pure/ML/ml_heap.scala
    Author:     Makarius

ML heap operations.
*/

package isabelle


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

  sealed case class Log_DB(uuid: String, content: Bytes)

  object private_data extends SQL.Data("isabelle_heaps") {
    override lazy val tables: SQL.Tables = SQL.Tables(Base.table, Slices.table)

    object Generic {
      val name = SQL.Column.string("name").make_primary_key
    }

    object Base {
      val name = Generic.name
      val heap_size = SQL.Column.long("heap_size")
      val heap_digest = SQL.Column.string("heap_digest")
      val uuid = SQL.Column.string("uuid")
      val log_db = SQL.Column.bytes("log_db")

      val table = make_table(List(name, heap_size, heap_digest, uuid, log_db))
    }

    object Size {
      val name = Generic.name
      val heap = SQL.Column.string("heap")
      val log_db = SQL.Column.string("log_db")

      val table = make_table(List(name, heap, log_db),
        body =
          "SELECT name, pg_size_pretty(heap_size::bigint) as heap, " +
          "  pg_size_pretty(length(log_db)::bigint) as log_db FROM " + Base.table.ident,
        name = "size")
    }

    object Slices {
      val name = Generic.name
      val slice = SQL.Column.int("slice").make_primary_key
      val content = SQL.Column.bytes("content")

      val table = make_table(List(name, slice, content), name = "slices")
    }

    object Slices_Size {
      val name = Generic.name
      val slice = Slices.slice
      val size = SQL.Column.string("size")

      val table = make_table(List(name, slice, size),
        body = "SELECT name, slice, pg_size_pretty(length(content)::bigint) as size FROM " +
          Slices.table.ident,
        name = "slices_size")
    }

    def read_digests(db: SQL.Database, names: Iterable[String]): Map[String, SHA1.Digest] =
      if (names.isEmpty) Map.empty
      else {
        db.execute_query_statement(
          Base.table.select(List(Base.name, Base.heap_digest),
            sql = Generic.name.where_member(names)),
          List.from[(String, String)],
          res => res.string(Base.name) -> res.string(Base.heap_digest)
        ).collect({
          case (name, digest) if digest.nonEmpty => name -> SHA1.fake_digest(digest)
        }).toMap
      }

    def read_slices(db: SQL.Database, name: String): List[Bytes] =
      db.execute_query_statement(
        Slices.table.select(List(Slices.content),
          sql = Generic.name.where_equal(name) + SQL.order_by(List(Slices.slice))),
        List.from[Bytes], _.bytes(Slices.content))

    def read_log_db(db: SQL.Database, name: String, old_uuid: String = ""): Option[Log_DB] =
      db.execute_query_statement(
        Base.table.select(List(Base.uuid, Base.log_db), sql =
          SQL.where_and(
            Generic.name.equal(name),
            if_proper(old_uuid, Base.uuid.ident + " <> " + SQL.string(old_uuid)))),
        List.from[(String, Bytes)],
        res => (res.string(Base.uuid), res.bytes(Base.log_db))
      ).collectFirst(
        {
          case (uuid, content) if uuid.nonEmpty && !content.is_empty =>
            Log_DB(uuid, content)
        })

    def write_slice(db: SQL.Database, name: String, slice: Int, content: Bytes): Unit =
      db.execute_statement(Slices.table.insert(), body =
      { stmt =>
        stmt.string(1) = name
        stmt.int(2) = slice
        stmt.bytes(3) = content
      })

    def clean_entry(db: SQL.Database, name: String): Unit = {
      for (table <- List(Base.table, Slices.table)) {
        db.execute_statement(table.delete(sql = Base.name.where_equal(name)))
      }
    }

    def init_entry(
      db: SQL.Database,
      name: String,
      heap_size: Long,
      heap_digest: Option[SHA1.Digest],
      log_db: Option[Log_DB]
    ): Unit = {
      clean_entry(db, name)
      for (table <- List(Size.table, Slices_Size.table)) {
        db.create_view(table)
      }
      db.execute_statement(Base.table.insert(), body =
        { stmt =>
          stmt.string(1) = name
          stmt.long(2) = heap_size
          stmt.string(3) = heap_digest.map(_.toString)
          stmt.string(4) = log_db.map(_.uuid)
          stmt.bytes(5) = log_db.map(_.content)
        })
    }

    def update_entry(
      db: SQL.Database,
      name: String,
      heap_size: Long,
      heap_digest: Option[SHA1.Digest],
      log_db: Option[Log_DB]
    ): Unit =
      db.execute_statement(
        Base.table.update(List(Base.heap_size, Base.heap_digest, Base.uuid, Base.log_db),
          sql = Base.name.where_equal(name)),
        body =
          { stmt =>
            stmt.long(1) = heap_size
            stmt.string(2) = heap_digest.map(_.toString)
            stmt.string(3) = log_db.map(_.uuid)
            stmt.bytes(4) = log_db.map(_.content)
          })
  }

  def clean_entry(db: SQL.Database, session_name: String): Unit =
    private_data.transaction_lock(db, create = true, label = "ML_Heap.clean_entry") {
      private_data.clean_entry(db, session_name)
    }

  def read_digests(db: SQL.Database, names: Iterable[String]): Map[String, SHA1.Digest] =
    if (names.isEmpty) Map.empty
    else {
      private_data.transaction_lock(db, create = true, label = "ML_Heap.read_digests") {
        private_data.read_digests(db, names)
      }
    }

  def store(
    db: SQL.Database,
    session: Store.Session,
    slice: Space,
    cache: Compress.Cache = Compress.Cache.none,
    progress: Progress = new Progress
  ): Unit = {
    val log_db =
      for {
        path <- session.log_db
        uuid <- proper_string(Store.read_build_uuid(path, session.name))
      } yield Log_DB(uuid, Bytes.read(path))

    val heap_digest = session.heap.map(write_file_digest)
    val heap_size =
      session.heap match {
        case Some(heap) => File.size(heap) - sha1_prefix.length - SHA1.digest_length
        case None => 0L
      }

    val slice_size = slice.bytes max Space.MiB(1).bytes
    val slices = (heap_size.toDouble / slice_size.toDouble).ceil.toInt
    val step = if (slices == 0) 0L else (heap_size.toDouble / slices.toDouble).ceil.toLong

    def slice_content(i: Int): Bytes = {
      val j = i + 1
      val offset = step * i
      val limit = if (j < slices) step * j else heap_size
      Bytes.read_file(session.the_heap, offset = offset, limit = limit)
        .compress(cache = cache)
    }

    try {
      if (slices > 0) progress.echo("Storing " + session.name + " ...")

      // init entry: slice 0 + initial log_db
      {
        val (heap_size0, heap_digest0) = if (slices > 1) (0L, None) else (heap_size, heap_digest)
        val log_db0 = if (slices <= 1) log_db else None
        val content0 = if (slices > 0) Some(slice_content(0)) else None

        if (log_db0.isDefined) progress.echo("Storing " + session.log_db_name + " ...")

        private_data.transaction_lock(db, create = true, label = "ML_Heap.store") {
          private_data.init_entry(db, session.name, heap_size0, heap_digest0, log_db0)
          for (content <- content0) private_data.write_slice(db, session.name, 0, content)
        }
      }

      // update entry: slice 1 ... + final log_db
      if (slices > 1) {
        for (i <- 1 until slices) {
          val content = slice_content(i)
          private_data.transaction_lock(db, label = "ML_Heap.store" + i) {
            private_data.write_slice(db, session.name, i, content)
          }
        }

        if (log_db.isDefined) progress.echo("Storing " + session.log_db_name + " ...")

        private_data.transaction_lock(db, label = "ML_Heap.store_update") {
          private_data.update_entry(db, session.name, heap_size, heap_digest, log_db)
        }
      }
    }
    catch { case exn: Throwable =>
      private_data.transaction_lock(db, create = true, label = "ML_Heap.store_clean") {
        private_data.clean_entry(db, session.name)
      }
      throw exn
    }
  }

  def restore(
    db: SQL.Database,
    sessions: List[Store.Session],
    cache: Compress.Cache = Compress.Cache.none,
    progress: Progress = new Progress
  ): Unit = {
    if (sessions.exists(_.defined)) {
      private_data.transaction_lock(db, create = true, label = "ML_Heap.restore") {
        /* heap */

        val defined_heaps =
          for (session <- sessions; heap <- session.heap)
            yield session.name -> heap

        val db_digests = private_data.read_digests(db, defined_heaps.map(_._1))

        for ((session_name, heap) <- defined_heaps) {
          val file_digest = read_file_digest(heap)
          val db_digest = db_digests.get(session_name)
          if (db_digest.isDefined && db_digest != file_digest) {
            progress.echo("Restoring " + session_name + " ...")

            val base_dir = Isabelle_System.make_directory(heap.expand.dir)
            Isabelle_System.with_tmp_file(session_name + "_", base_dir = base_dir.file) { tmp =>
              tmp.file.delete()
              for (slice <- private_data.read_slices(db, session_name)) {
                Bytes.append(tmp, slice.uncompress(cache = cache))
              }
              val digest = write_file_digest(tmp)
              if (db_digest.get == digest) Isabelle_System.move_file(tmp, heap)
              else error("Incoherent content for session heap " + heap.expand)
            }
          }
        }


        /* log_db */

        for (session <- sessions; path <- session.log_db) {
          val file_uuid = Store.read_build_uuid(path, session.name)
          private_data.read_log_db(db, session.name, old_uuid = file_uuid) match {
            case Some(log_db) if file_uuid.isEmpty =>
              progress.echo("Restoring " + session.log_db_name + " ...")
              Isabelle_System.make_directory(path.expand.dir)
              Bytes.write(path, log_db.content)
            case Some(_) => error("Incoherent content for session database " + path.expand)
            case None =>
          }
        }
      }
    }
  }
}
