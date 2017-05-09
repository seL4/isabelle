/*  Title:      Pure/Admin/isabelle_devel.scala
    Author:     Makarius

Website for Isabelle development resources.
*/

package isabelle


object Isabelle_Devel
{
  val root = Path.explode("~/html-data/devel")

  val RELEASE_SNAPSHOT = "release_snapshot"
  val BUILD_LOG_DB = "build_log.db"
  val BUILD_STATUS = "build_status"

  val standard_log_dirs =
    List(Path.explode("~/log"), Path.explode("~/afp/log"), Path.explode("~/cronjob/log"))

  val build_status_dir = root + Path.explode(BUILD_STATUS)


  /* index */

  def make_index()
  {
    val header = "Isabelle Development Resources"

    Isabelle_System.mkdirs(root)
    File.write(root + Path.explode("index.html"),
      HTML.output_document(
        List(HTML.title(header)),
        List(HTML.chapter(header),
          HTML.itemize(
            List(
              HTML.text("Isabelle nightly ") :::
              List(HTML.link(RELEASE_SNAPSHOT, HTML.text("release snapshot"))) :::
              HTML.text(" (for all platforms)"),

              HTML.text("Isabelle ") :::
              List(HTML.link(BUILD_STATUS + "/index.html", HTML.text("build status"))) :::
              HTML.text(" information"),

              HTML.text("Database with recent ") :::
              List(HTML.link(BUILD_LOG_DB, HTML.text("build log"))) :::
              HTML.text(" information (e.g. for ") :::
              List(HTML.link("http://sqlitebrowser.org",
                List(HTML.code(HTML.text("sqlitebrowser"))))))))))
  }


  /* release snapshot */

  def release_snapshot(
    rev: String = "",
    afp_rev: String = "",
    parallel_jobs: Int = 1,
    remote_mac: String = "")
  {
    Isabelle_System.with_tmp_dir("isadist")(base_dir =>
      {
        val release_snapshot_dir = root + Path.explode(RELEASE_SNAPSHOT)

        val new_snapshot = release_snapshot_dir.ext("new")
        val old_snapshot = release_snapshot_dir.ext("old")

        Isabelle_System.rm_tree(new_snapshot)
        Isabelle_System.rm_tree(old_snapshot)

        Build_Release.build_release(base_dir, rev = rev, afp_rev = afp_rev,
          parallel_jobs = parallel_jobs, remote_mac = remote_mac, website = Some(new_snapshot))

        if (release_snapshot_dir.is_dir) File.move(release_snapshot_dir, old_snapshot)
        File.move(new_snapshot, release_snapshot_dir)
        Isabelle_System.rm_tree(old_snapshot)
      })
  }


  /* maintain build_log database */

  def build_log_database(options: Options, log_dirs: List[Path] = standard_log_dirs)
  {
    val store = Build_Log.store(options)
    using(store.open_database())(db =>
    {
      store.update_database(db, log_dirs, ml_statistics = true)
      store.snapshot_database(db, root + Path.explode(BUILD_LOG_DB))
    })
  }
}
