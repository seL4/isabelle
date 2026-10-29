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

    def print(relevant: Profiling.Percentage = Profiling.permille(0)): String = {
      val relevant_entries =
        entries.filter(entry => entry.percentage(total_account).permille >= relevant.permille)
      ("profile_" + kind + ":\n") +
      cat_lines((relevant_entries ::: List(total)).map(_.print(total_account)))
    }
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



  /** report from session build database */

  def profiling_report(
    options: Options,
    session: String,
    theories: List[String] = Nil,
    clean_name: Boolean = false,
    relevant: Profiling.Percentage = Profiling.permille(0),
    progress: Progress = new Progress
  ): Unit = {
    val store = Store(options)

    using(Export.open_session_context0(store, session)) { session_context =>
      session_context.session_db().map(db => store.read_theories(db, session)) match {
        case None => store.error_database(session)
        case Some(used_theories) =>
          theories.filterNot(used_theories.toSet) match {
            case Nil =>
            case bad => error("Unknown theories " + commas_quote(bad))
          }
          val reports =
            (for {
              thy <- used_theories.iterator
              if theories.isEmpty || theories.contains(thy)
              snapshot <- Build.read_theory(session_context.theory(thy)).iterator
              case (Protocol.ML_Profiling(_, report), _) <- snapshot.messages.iterator
            } yield if (clean_name) report.clean_name else report).toList

          for (report <- account(reports)) {
            progress.echo(report.print(relevant = relevant))
          }
      }
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("profiling_report", "report Poly/ML profiling information from log files",
      Scala_Project.here,
      { args =>
        var theories: List[String] = Nil
        var clean_name = false
        var options = Options.init()
        var relevant = Profiling.permille(0)

        val getopts = Getopts("""
Usage: isabelle profiling_report [OPTIONS] SESSION

  Options are:
    -T NAME      restrict to given theories (multiple options possible)
    -c           clean function names
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -r PERMILLE  lower bound for relevant entries (in permille)

  Report Poly/ML profiling from the sebuild database of the given session
  (without up-to-date check of sources).
""",
          "T:" -> (arg => theories = theories ::: List(arg)),
          "c" -> (_ => clean_name = true),
          "o:" -> (arg => options = options + arg),
          "r:" -> (arg => relevant = Profiling.permille(Value.Int.parse(arg))))

        val more_args = getopts(args)
        val session_name =
          more_args match {
            case List(session_name) => session_name
            case _ => getopts.usage()
          }

        val progress = new Console_Progress()

        profiling_report(options, session_name, theories = theories,
          clean_name = clean_name, relevant = relevant, progress = progress)
      })
}
