/*  Title:      Pure/Admin/ci_build_benchmark.scala
    Author:     Lars Hupel and Fabian Huch, TU Munich

CI benchmark build profile.
*/

package isabelle


object CI_Build_Benchmark {

  val isabelle_tool = Isabelle_Tool("ci_build_benchmark", "builds Isabelle benchmarks + timing group",
    Scala_Project.here,
  { args =>
    val getopts = Getopts("""
Usage: isabelle ci_build_benchmark

  Builds Isabelle benchmark and timing sessions.
    """)
    getopts(args)

    val selection = Sessions.Selection(session_groups = List("timing"))
    val profile = CI_Profile.Profile(threads = 6, jobs = 1, numa = false)
    val config = CI_Profile.Build_Config(documents = false,
      select = List(Path.explode("$ISABELLE_HOME/src/Benchmarks")), selection = selection)

    CI_Profile.build(profile, config)
  })
}
