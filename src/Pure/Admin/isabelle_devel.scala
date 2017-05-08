/*  Title:      Pure/Admin/isabelle_devel.scala
    Author:     Makarius

Website for Isabelle development resources.
*/

package isabelle


object Isabelle_Devel
{
  val root_dir = Path.explode("~/html-data/devel")

  val release_snapshot_dir = root_dir + Path.explode("release_snapshot")
  val build_log_db = root_dir + Path.explode("build_log.db")
  val build_status_dir = root_dir + Path.explode("build_status")

  val log_dirs =
    List(Path.explode("~/log"), Path.explode("~/afp/log"), Path.explode("~/cronjob/log"))


  /* release snapshot */

  def release_snapshot(
    rev: String = "",
    afp_rev: String = "",
    parallel_jobs: Int = 1,
    remote_mac: String = "")
  {
    Isabelle_System.with_tmp_dir("isadist")(base_dir =>
      {
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

  def build_log_database(options: Options)
  {
    val store = Build_Log.store(options)
    using(store.open_database())(db =>
    {
      store.update_database(db, log_dirs, ml_statistics = true)
      store.snapshot_database(db, build_log_db)
    })
  }


  /* present build status */

  def build_status(options: Options)
  {
    val data = Build_Status.read_data(options)
    Build_Status.present_data(data, target_dir = build_status_dir)
  }
}
