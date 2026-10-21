/*  Title:      Pure/ML/ml_profiling.scala
    Author:     Makarius

ML profiling (via Poly/ML run-time system).
*/

package isabelle


import scala.collection.immutable.SortedMap


object ML_Profiling {
  sealed case class Entry(name: String, count: Long) {
    def clean_name: Entry = copy(name = """-?\(\d+\).*$""".r.replaceAllIn(name, ""))

    def print(total_count: Long): String = {
      val p = Profiling.percentage(count, total_count).permille / 1000.0
      Library.format("%12d %.3f %s", Value.Long.obj(count), Value.Double.obj(p), name)
    }
  }

  sealed case class Report(kind: String, entries: List[Entry]) {
    def clean_name: Report = copy(entries = entries.map(_.clean_name))

    lazy val total_count: Long = entries.iterator.map(_.count).sum
    def total: Entry = Entry("TOTAL", total_count)

    def print: String =
      ("profile_" + kind + ":\n") + cat_lines((entries ::: List(total)).map(_.print(total_count)))
  }

  def account(reports: List[Report]): List[Report] = {
    val empty = SortedMap.empty[String, Long].withDefaultValue(0L)
    var results = SortedMap.empty[String, SortedMap[String, Long]].withDefaultValue(empty)
    for (report <- reports) {
      val kind = report.kind
      val map = report.entries.foldLeft(results(kind))(
        (m, e) => m + (e.name -> (e.count + m(e.name))))
      results = results + (kind -> map)
    }
    for ((kind, map) <- results.toList)
      yield Report(kind, for ((name, count) <- map.toList.sortBy(_._2)) yield Entry(name, count))
  }
}
