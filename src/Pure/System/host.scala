/*  Title:      Pure/System/host.scala
    Author:     Makarius

Information about compute hosts.
*/

package isabelle


object Host {
  /* allocated resources */

  object Node_Info { def none: Node_Info = Node_Info("", None) }

  sealed case class Node_Info(hostname: String, numa_node: Option[Int])


  /* SQL data model */

  object Data {
    def make_table(name: String, columns: List[SQL.Column], body: String = ""): SQL.Table =
      SQL.Table("isabelle_host" + if_proper(name, "_" + name), columns, body = body)

    object Node_Info {
      val hostname = SQL.Column.string("hostname").make_primary_key
      val numa_index = SQL.Column.int("numa_index")

      val table = make_table("node_info", List(hostname, numa_index))
    }

    def read_numa_index(db: SQL.Database, hostname: String): Int =
      db.using_statement(
        Node_Info.table.select(List(Node_Info.numa_index),
          sql = Node_Info.hostname.where_equal(hostname))
      )(stmt => stmt.execute_query().iterator(_.int(Node_Info.numa_index)).nextOption.getOrElse(0))

    def update_numa_index(db: SQL.Database, hostname: String, numa_index: Int): Boolean =
      if (read_numa_index(db, hostname) != numa_index) {
        db.using_statement(
          Node_Info.table.delete(sql = Node_Info.hostname.where_equal(hostname))
        )(_.execute())
        db.using_statement(Node_Info.table.insert()) { stmt =>
          stmt.string(1) = hostname
          stmt.int(2) = numa_index
          stmt.execute()
        }
        true
      }
      else false
  }
}
