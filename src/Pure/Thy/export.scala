/*  Title:      Pure/Thy/export.scala
    Author:     Makarius

Manage theory exports: compressed blobs.
*/

package isabelle

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

    def where_equal(session_name: String, theory_name: String): SQL.Source =
      "WHERE " + Data.session_name.equal(session_name) +
      " AND " + Data.theory_name.equal(theory_name)
  }

  def read_names(db: SQL.Database, session_name: String, theory_name: String): List[String] =
  {
    val select = Data.table.select(List(Data.name), Data.where_equal(session_name, theory_name))
    db.using_statement(select)(stmt =>
      stmt.execute_query().iterator(res => res.string(Data.name)).toList)
  }

  def read_name(db: SQL.Database, session_name: String, theory_name: String, name: String): Boolean =
  {
    val select =
      Data.table.select(List(Data.name),
        Data.where_equal(session_name, theory_name) + " AND " + Data.name.equal(name))
    db.using_statement(select)(stmt => stmt.execute_query().next())
  }

  def message(msg: String, theory_name: String, name: String): String =
    msg + " " + quote(name) + " for theory " + quote(theory_name)

  sealed case class Entry(
    session_name: String,
    theory_name: String,
    name: String,
    compressed: Boolean,
    body: Future[Bytes])
  {
    override def toString: String = theory_name + ":" + name

    def write(db: SQL.Database)
    {
      val bytes = body.join
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
  }

  def make_entry(session_name: String, args: Markup.Export.Args, body: Bytes): Entry =
  {
    Entry(session_name, args.theory_name, args.name, args.compress,
      if (args.compress) Future.fork(body.compress()) else Future.value(body))
  }

  def read_entry(db: SQL.Database, session_name: String, theory_name: String, name: String): Entry =
  {
    val select =
      Data.table.select(List(Data.compressed, Data.body),
        Data.where_equal(session_name, theory_name) + " AND " + Data.name.equal(name))
    db.using_statement(select)(stmt =>
    {
      val res = stmt.execute_query()
      if (res.next()) {
        val compressed = res.bool(Data.compressed)
        val body = res.bytes(Data.body)
        Entry(session_name, theory_name, name, compressed, Future.value(body))
      }
      else error(message("Bad export", theory_name, name))
    })
  }


  /* database consumer thread */

  def consumer(db: SQL.Database): Consumer = new Consumer(db)

  class Consumer private[Export](db: SQL.Database)
  {
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
      consumer.send(make_entry(session_name, args, body))

    def shutdown(close: Boolean = false): List[String] =
    {
      consumer.shutdown()
      if (close) db.close()
      export_errors.value.reverse
    }
  }
}
