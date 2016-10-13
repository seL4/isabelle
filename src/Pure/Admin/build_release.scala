/*  Title:      Pure/Admin/build_release.scala
    Author:     Makarius

Build full Isabelle distribution from repository.
*/

package isabelle


object Build_Release
{
  def build_release(base_dir: Path,
    progress: Progress = Ignore_Progress,
    rev: String = "",
    official_release: Boolean = false,
    release_name: String = "",
    build_library: Boolean = false,
    parallel_jobs: Int = 1,
    remote_mac: String = "")
  {
    /* release info */

    val release_date = Date.now()

    val distribution_name =
      if (release_name != "") release_name
      else "Isabelle_" + Date.Format.date(release_date)

    val distribution_dir = base_dir + Path.explode("dist-" + distribution_name)


    /* make distribution */

    progress.bash(
      "isabelle makedist -d " + File.bash_path(base_dir) + " -j" + parallel_jobs.toString +
        (if (official_release) " -O" else "") +
        (if (release_name != "") " -r " + File.bash_string(release_name) else "") +
        (if (rev != "") " " + File.bash_string(rev) else ""),
      echo = true).check


    /* make application bundles */

    for (platform_family <- List("linux", "windows", "windows64", "macos")) {
      progress.echo("\n*** " + platform_family + " ***")
      progress.bash(
        "isabelle makedist_bundle " +
          File.bash_path(distribution_dir + Path.explode(distribution_name + ".tar.gz")) +
          " " + File.bash_string(platform_family) +
          (if (remote_mac == "") "" else " " + File.bash_string(remote_mac)),
        echo = true).check
    }


    /* minimal website */

    File.write(distribution_dir + Path.explode("index.html"),
"""<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 3.2//EN">
<html>
<head>
<title>""" + HTML.output(distribution_name) + """</title>
</head>

<body>
<h1>""" + HTML.output(distribution_name) + """</h1>
<ul>
<li><a href=""" + "\"" + HTML.output(distribution_name) + """_app.tar.gz">Linux</a></li>
<li><a href=""" + "\"" + HTML.output(distribution_name) + """-win32.exe">Windows</a></li>
<li><a href=""" + "\"" + HTML.output(distribution_name) + """-win64.exe">Windows (64bit)</a></li>
<li><a href=""" + "\"" + HTML.output(distribution_name) + """.dmg">Mac OS X</a></li>
</ul>
</body>

</html>
""")


    /* HTML library */

    if (build_library)
      progress.bash("\"$ISABELLE_HOME/Admin/Release/build_library\" -j" + parallel_jobs.toString +
        File.bash_path(distribution_dir +
          Path.explode(distribution_name + "_" +
            Isabelle_System.getenv_strict("ISABELLE_PLATFORM_FAMILY") + ".tar.gz"))).check
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
      var rev = ""

      val getopts = Getopts("""
Usage: Admin/build_release [OPTIONS] BASE_DIR

  Options are:
    -M USER@HOST remote Mac OS X for dmg build
    -O           official release (not release-candidate)
    -R RELEASE   proper release with name
    -j INT       maximum number of parallel jobs (default 1)
    -l           build library
    -r REV       Mercurial changeset id (default: RELEASE or tip)

  Build Isabelle release in base directory, using the local repository clone.
""",
        "M:" -> (arg => remote_mac = arg),
        "O" -> (_ => official_release = true),
        "R:" -> (arg => release_name = arg),
        "j:" -> (arg => parallel_jobs = Value.Int.parse(arg)),
        "l" -> (_ => build_library))

      val more_args = getopts(args)
      val base_dir = more_args match { case List(base_dir) => base_dir case _ => getopts.usage() }

      val progress = new Console_Progress()

      build_release(Path.explode(base_dir), progress = progress, rev = rev,
        official_release = official_release, release_name = release_name,
        build_library = build_library, parallel_jobs = parallel_jobs, remote_mac = remote_mac)
    }
  }
}
