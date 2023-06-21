/*  Title:      Pure/System/host.scala
    Author:     Makarius

Information about compute hosts, including NUMA: Non-Uniform Memory Access of
separate CPU nodes.

See also https://www.open-mpi.org/projects/hwloc --- notably "lstopo" or
"hwloc-ls" (e.g. via Ubuntu package "hwloc").
*/

package isabelle


object Host {
  /* process policy via numactl tool */

  def numactl(node: Int): String = "numactl -m" + node + " -N" + node
  def numactl_ok(node: Int): Boolean = Isabelle_System.bash(numactl(node) + " true").ok

  def process_policy(options: Options, numa_node: Option[Int]): Options =
    numa_node match {
      case None => options
      case Some(node) =>
        options.string("process_policy") = if (numactl_ok(node)) numactl(node) else ""
    }


  /* allocated resources */

  object Node_Info { def none: Node_Info = Node_Info("", None) }

  sealed case class Node_Info(hostname: String, numa_node: Option[Int]) {
    override def toString: String =
      hostname + if_proper(numa_node, "/" + numa_node.get.toString)

    def process_policy(options: Options): Options =
      Host.process_policy(options, numa_node)
  }


  /* available NUMA nodes */

  private val numa_info_linux: Path = Path.explode("/sys/devices/system/node/online")

  def numa_nodes(enabled: Boolean = true, ssh: SSH.System = SSH.Local): List[Int] = {
    val Single = """^(\d+)$""".r
    val Multiple = """^(\d+)-(\d+)$""".r

    def parse(s: String): List[Int] =
      s match {
        case Single(Value.Int(i)) => List(i)
        case Multiple(Value.Int(i), Value.Int(j)) => (i to j).toList
        case _ => error("Cannot parse CPU NUMA node specification: " + quote(s))
      }

    val numa_info = if (ssh.isabelle_platform.is_linux) Some(numa_info_linux) else None
    for {
      path <- numa_info.toList
      if enabled && ssh.is_file(path)
      s <- space_explode(',', ssh.read(path).trim)
      n <- parse(s)
    } yield n
  }

  def numa_node0(): Option[Int] =
    try {
      numa_nodes() match {
        case ns if ns.length >= 2 && numactl_ok(ns.head) => Some(ns.head)
        case _ => None
      }
    }
    catch { case ERROR(_) => None }



  /* shuffling of NUMA nodes */

  def numa_check(progress: Progress, enabled: Boolean): Boolean = {
    def warning =
      numa_nodes() match {
        case ns if ns.length < 2 => Some("no NUMA nodes available")
        case ns if !numactl_ok(ns.head) => Some("bad numactl tool")
        case _ => None
      }

    enabled &&
      (warning match {
        case Some(s) =>
          progress.echo_warning("Shuffling of NUMA CPU nodes is disabled: " + s)
          false
        case _ => true
      })
  }


  /* SQL data model */

  object Data extends SQL.Data("isabelle_host") {
    val database: Path = Path.explode("$ISABELLE_HOME_USER/host.db")

    override lazy val tables = SQL.Tables(Node_Info.table)

    object Node_Info {
      val hostname = SQL.Column.string("hostname").make_primary_key
      val numa_next = SQL.Column.int("numa_next")

      val table = make_table("node_info", List(hostname, numa_next))
    }

    def read_numa_next(db: SQL.Database, hostname: String): Int =
      db.execute_query_statementO[Int](
        Node_Info.table.select(List(Node_Info.numa_next),
          sql = Node_Info.hostname.where_equal(hostname)),
        res => res.int(Node_Info.numa_next)
      ).getOrElse(0)

    def write_numa_next(db: SQL.Database, hostname: String, numa_next: Int): Unit = {
      db.execute_statement(Node_Info.table.delete(sql = Node_Info.hostname.where_equal(hostname)))
      db.execute_statement(Node_Info.table.insert(), body =
        { stmt =>
          stmt.string(1) = hostname
          stmt.int(2) = numa_next
        })
    }
  }

  def next_numa_node(
    db: SQL.Database,
    hostname: String,
    available_nodes: List[Int],
    used_nodes: => Set[Int]
  ): Option[Int] =
    if (available_nodes.isEmpty) None
    else {
      val available = available_nodes.zipWithIndex
      val used = used_nodes
      Data.transaction_lock(db, create = true) {
        val numa_next = Data.read_numa_next(db, hostname)
        val numa_index = available.collectFirst({ case (n, i) if n == numa_next => i }).getOrElse(0)
        val candidates = available.drop(numa_index) ::: available.take(numa_index)
        val (n, i) =
          candidates.find({ case (n, i) => i == numa_index && !used(n) }) orElse
          candidates.find({ case (n, _) => !used(n) }) getOrElse candidates.head

        val numa_next1 = available_nodes((i + 1) % available_nodes.length)
        if (numa_next != numa_next1) Data.write_numa_next(db, hostname, numa_next1)

        Some(n)
      }
    }
}
