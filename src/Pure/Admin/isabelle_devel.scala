/*  Title:      Pure/Admin/isabelle_devel.scala
    Author:     Makarius

Website for Isabelle development resources.
*/

package isabelle


object Isabelle_Devel
{
  val RELEASE_SNAPSHOT = "release_snapshot"
  val BUILD_LOG_DB = "build_log.db"
  val BUILD_STATUS = "build_status"
  val CRONJOB_LOG = "cronjob-main.log"

  val root = Path.explode("~/html-data/devel")
  val cronjob_log = root + Path.basic(CRONJOB_LOG)


  /* index */

  def make_index()
  {
    val header = "Isabelle Development Resources"

    HTML.write_document(root, "index.html",
      List(HTML.title(header)),
      List(HTML.chapter(header),
        HTML.itemize(
          List(
            HTML.text("Isabelle nightly ") :::
            List(HTML.link(RELEASE_SNAPSHOT, HTML.text("release snapshot"))) :::
            HTML.text(" (for all platforms)"),

            HTML.text("Cronjob ") ::: List(HTML.link(CRONJOB_LOG, HTML.text("log file"))),

            HTML.text("Isabelle ") :::
            List(HTML.link(BUILD_STATUS + "/index.html", HTML.text("build status"))) :::
            HTML.text(" information"),

            HTML.text("Database with recent ") :::
            List(HTML.link(BUILD_LOG_DB, HTML.text("build log"))) :::
            HTML.text(" information (e.g. for ") :::
            List(HTML.link("https://sqlitebrowser.org",
              List(HTML.code(HTML.text("sqlitebrowser"))))) :::
            HTML.text(")")))))
  }


  /* release snapshot */

  def release_snapshot(
    options: Options,
    rev: String = "",
    afp_rev: String = "",
    parallel_jobs: Int = 1,
    remote_mac: String = "")
  {
    Isabelle_System.with_tmp_dir("isadist")(base_dir =>
      {
        Isabelle_System.update_directory(root + Path.explode(RELEASE_SNAPSHOT),
          website_dir =>
            Build_Release.build_release(base_dir, options, rev = rev, afp_rev = afp_rev,
              parallel_jobs = parallel_jobs, remote_mac = remote_mac, website = Some(website_dir)))
      })
  }


  /* maintain build_log database */

  def build_log_database(options: Options, log_dirs: List[Path])
  {
    val store = Build_Log.store(options)
    using(store.open_database())(db =>
    {
      store.update_database(db, log_dirs)
      store.update_database(db, log_dirs, ml_statistics = true)
      store.snapshot_database(db, root + Path.explode(BUILD_LOG_DB))
    })
  }


  /* present build status */

  def build_status(options: Options)
  {
    Isabelle_System.update_directory(root + Path.explode(BUILD_STATUS),
      dir => Build_Status.build_status(options, target_dir = dir, ml_statistics = true))
  }
}
