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

  val root: Path = Path.explode("~/html-data/devel")
  val cronjob_log: Path = root + Path.basic(CRONJOB_LOG)


  /* index */

  def make_index(): Unit =
  {
    val redirect = "https://isabelle-dev.sketis.net/home/menu/view/20"

    HTML.write_document(root, "index.html",
      List(
        XML.Elem(Markup("meta",
          List("http-equiv" -> "Refresh", "content" -> ("0; url=" + redirect))), Nil)),
      List(HTML.link(redirect, HTML.text("Isabelle Development Resources"))))
  }


  /* release snapshot */

  def release_snapshot(
    options: Options,
    rev: String = "",
    afp_rev: String = "",
    parallel_jobs: Int = 1): Unit =
  {
    Isabelle_System.with_tmp_dir("isadist")(target_dir =>
      {
        Isabelle_System.update_directory(root + Path.explode(RELEASE_SNAPSHOT),
          website_dir =>
            Build_Release.build_release(options, target_dir = target_dir,
              rev = rev,
              afp_rev = afp_rev,
              parallel_jobs = parallel_jobs,
              build_sessions = List(Isabelle_System.getenv("ISABELLE_LOGIC")),
              website = Some(website_dir)))
      })
  }


  /* maintain build_log database */

  def build_log_database(options: Options, log_dirs: List[Path]): Unit =
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

  def build_status(options: Options): Unit =
  {
    Isabelle_System.update_directory(root + Path.explode(BUILD_STATUS),
      dir => Build_Status.build_status(options, target_dir = dir, ml_statistics = true))
  }
}
