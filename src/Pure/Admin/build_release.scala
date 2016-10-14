/*  Title:      Pure/Admin/build_release.scala
    Author:     Makarius

Build full Isabelle distribution from repository.
*/

package isabelle


object Build_Release
{
  sealed case class Release_Info(
    date: Date, name: String, dist_dir: Path, dist_archive: Path, dist_library_archive: Path)

  private val all_platform_families = List("linux", "windows", "windows64", "macos")

  def build_release(base_dir: Path,
    progress: Progress = Ignore_Progress,
    rev: String = "",
    official_release: Boolean = false,
    release_name: String = "",
    platform_families: List[String] = all_platform_families,
    build_library: Boolean = false,
    parallel_jobs: Int = 1,
    remote_mac: String = ""): Release_Info =
  {
    /* release info */

    val release_info =
    {
      val date = Date.now()
      val name = if (release_name != "") release_name else "Isabelle_" + Date.Format.date(date)
      val dist_dir = base_dir + Path.explode("dist-" + name)
      val dist_archive = dist_dir + Path.explode(name + ".tar.gz")
      val dist_library_archive = dist_dir + Path.explode(name + "_library.tar.gz")
      Release_Info(date, name, dist_dir, dist_archive, dist_library_archive)
    }

    val all_platform_bundles =
      Map("linux" -> (release_info.name + "_app.tar.gz"),
        "windows" -> (release_info.name + "-win32.exe"),
        "windows64" -> (release_info.name + "-win64.exe"),
        "macos" -> (release_info.name + ".dmg"))

    val platform_bundles =
      for (platform_family <- platform_families) yield {
        all_platform_bundles.get(platform_family) match {
          case None => error("Unknown platform family " + quote(platform_family))
          case Some(bundle) => (platform_family, bundle)
        }
      }


    /* make distribution */

    val jobs_option = " -j" + parallel_jobs.toString

    if (release_info.dist_archive.is_file)
      progress.echo("### Release archive already exists: " + release_info.dist_archive)
    else {
      progress.echo("Producing release archive " + release_info.dist_archive + " ...")
      progress.bash(
        "isabelle makedist -d " + File.bash_path(base_dir) + jobs_option +
          (if (official_release) " -O" else "") +
          (if (release_name != "") " -r " + File.bash_string(release_name) else "") +
          (if (rev != "") " " + File.bash_string(rev) else ""),
        echo = true).check
    }


    /* make application bundles */

    for ((platform_family, platform_bundle) <- platform_bundles) {
      val bundle_archive =
        release_info.dist_dir +
          Path.explode(
            if (platform_family == "macos" && remote_mac.isEmpty)
              release_info.name + "_dmg.tar.gz"
            else platform_bundle)
      if (bundle_archive.is_file)
        progress.echo("### Application bundle already exists: " + bundle_archive)
      else {
        progress.echo("\n*** " + platform_family + ": " + bundle_archive + " ***")
        progress.bash(
          "isabelle makedist_bundle " + File.bash_path(release_info.dist_archive) +
            " " + File.bash_string(platform_family) +
            (if (remote_mac == "") "" else " " + File.bash_string(remote_mac)),
          echo = true).check
      }
    }


    /* minimal website */

    val existing_platform_bundles =
      for {
        (a, b) <- all_platform_bundles
        p = release_info.dist_dir + Path.explode(b)
        if p.is_file
      } yield (a, b)

    File.write(release_info.dist_dir + Path.explode("index.html"),
"""<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 3.2//EN">
<html>
<head>
<title>""" + HTML.output(release_info.name) + """</title>
</head>

<body>
<h1>""" + HTML.output(release_info.name) + """</h1>
<ul>
""" +
  cat_lines(existing_platform_bundles.map({ case (a, b) =>
    "<li><a href=" + quote(HTML.output(a)) + ">" + HTML.output(b) + "</a></li>" })) +
"""
</ul>
</body>

</html>
""")


    /* HTML library */

    if (build_library) {
      if (release_info.dist_library_archive.is_file)
        progress.echo("### Library archive already exists: " + release_info.dist_library_archive)
      else {
        progress.bash("\"$ISABELLE_HOME/Admin/Release/build_library\"" + jobs_option + " " +
          File.bash_path(release_info.dist_dir +
            Path.explode(release_info.name + "_" +
              Isabelle_System.getenv_strict("ISABELLE_PLATFORM_FAMILY") + ".tar.gz"))).check
      }
    }


    release_info
  }



  /** command line entry point **/

  def main(args: Array[String])
  {
    Command_Line.tool0 {
      var remote_mac = ""
      var official_release = false
      var release_name = ""
      var parallel_jobs = 1
      var build_library = false
      var platform_families = all_platform_families
      var rev = ""

      val getopts = Getopts("""
Usage: Admin/build_release [OPTIONS] BASE_DIR

  Options are:
    -M USER@HOST remote Mac OS X for dmg build
    -O           official release (not release-candidate)
    -R RELEASE   proper release with name
    -j INT       maximum number of parallel jobs (default 1)
    -l           build library
    -p NAMES     platform families (comma separated list, default: """ +
      all_platform_families.mkString(",") + """)
    -r REV       Mercurial changeset id (default: RELEASE or tip)

  Build Isabelle release in base directory, using the local repository clone.
""",
        "M:" -> (arg => remote_mac = arg),
        "O" -> (_ => official_release = true),
        "R:" -> (arg => release_name = arg),
        "j:" -> (arg => parallel_jobs = Value.Int.parse(arg)),
        "l" -> (_ => build_library),
        "p:" -> (arg => platform_families = Library.space_explode(',', arg)),
        "r:" -> (arg => rev = arg))

      val more_args = getopts(args)
      val base_dir = more_args match { case List(base_dir) => base_dir case _ => getopts.usage() }

      val progress = new Console_Progress()

      build_release(Path.explode(base_dir), progress = progress, rev = rev,
        official_release = official_release, release_name = release_name,
        platform_families =
          if (platform_families.isEmpty) all_platform_families else platform_families,
        build_library = build_library, parallel_jobs = parallel_jobs, remote_mac = remote_mac)
    }
  }
}
