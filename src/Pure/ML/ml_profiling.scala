/*  Title:      Pure/ML/ml_profiling.scala
    Author:     Makarius

ML profiling.
*/

package isabelle


import java.util.Locale

import scala.collection.immutable.SortedMap


object ML_Profiling
{
  sealed case class Entry(name: String, count: Long)
  {
    def clean_name: Entry = copy(name = """-?\(\d+\).*$""".r.replaceAllIn(name, ""))

    def print: String =
      String.format(Locale.ROOT, "%10d %s",
        count.asInstanceOf[AnyRef], name.asInstanceOf[AnyRef])
  }

  sealed case class Report(kind: String, entries: List[Entry])
  {
    def clean_name: Report = copy(entries = entries.map(_.clean_name))

    def total: Entry = Entry("TOTAL", entries.iterator.map(_.count).sum)

    def print: String =
    {
      (if (kind == "time_thread") "time profile (single thread)" else kind + " profile") +
        (entries ::: List(total)).map(_.print).mkString(":\n", "\n", "\n")
    }
  }

  def account(reports: List[Report]): List[Report] =
  {
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
