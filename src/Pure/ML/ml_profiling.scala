/*  Title:      Pure/ML/ml_profiling.scala
    Author:     Makarius

ML profiling (via Poly/ML run-time system).
*/

package isabelle


import scala.collection.immutable.SortedMap


object ML_Profiling {
  sealed case class Entry(name: String, count: Long) {
    def clean_name: Entry = copy(name = """-?\(\d+\).*$""".r.replaceAllIn(name, ""))

    def account: Long = if (name == "GARBAGE COLLECTION (total)") 0 else count

    def percentage(total_account: Long): Profiling.Percentage =
      Profiling.percentage(count, total_account)

    def print_percentage(total_account: Long): String =
      Library.format("%.3f", Value.Double.obj(percentage(total_account).permille / 1000.0))

    def print(total_account: Long): String =
      Library.format("%12d %s %s", Value.Long.obj(count), print_percentage(total_account), name)
  }

  sealed case class Report(kind: String, entries: List[Entry]) {
    def clean_name: Report = copy(entries = entries.map(_.clean_name))

    lazy val total_account: Long = entries.iterator.map(_.account).sum
    def total: Entry = Entry("TOTAL", total_account)

    def print: String =
      ("profile_" + kind + ":\n") + cat_lines((entries ::: List(total)).map(_.print(total_account)))
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
