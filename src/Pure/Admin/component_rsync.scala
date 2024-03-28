/*  Title:      Pure/Admin/component_rsync.scala
    Author:     Makarius

Build Isabelle rsync component from official source distribution.
*/

package isabelle


object Component_Rsync {
  /* resources */

  def home: Path = Path.explode("$ISABELLE_RSYNC_HOME")

  def local_program: Path = Path.explode("$ISABELLE_RSYNC")

  def remote_program(directory: Components.Directory): Path = {
    val platform = "platform_" + directory.ssh.isabelle_platform.ISABELLE_PLATFORM64
    directory.path + Path.basic(platform) + Path.basic("rsync")
  }


  /* build rsync */

  val default_version = "3.2.7"
  val default_download_url = "https://github.com/WayneD/rsync/archive/refs/tags"
  val default_build_options: List[String] =
    List(
      "--disable-acl-support",
      "--disable-lz4",
      "--disable-md2man",
      "--disable-openssl",
      "--disable-xattr-support",
      "--disable-xxhash",
      "--disable-zstd")

  def build_rsync(
    version: String = default_version,
    download_url: String = default_download_url,
    progress: Progress = new Progress,
    target_dir: Path = Path.current,
    build_options: List[String] = default_build_options
  ): Unit = {
    Isabelle_System.with_tmp_dir("build") { tmp_dir =>
      /* component */

      val component_name = "rsync-" + version
      val component_dir =
        Components.Directory(target_dir + Path.basic(component_name)).create(progress = progress)

      val platform_name = Isabelle_Platform.self.ISABELLE_PLATFORM()
      val platform_dir =
        Isabelle_System.make_directory(component_dir.path + Path.basic("platform_" + platform_name))


      /* download source */

      val archive_name = "v" + version + ".tar.gz"
      val archive_path = tmp_dir + Path.explode(archive_name)
      val archive_url = Url.append_path(download_url, archive_name)
      Isabelle_System.download_file(archive_url, archive_path, progress = progress)

      Isabelle_System.extract(archive_path, tmp_dir)
      val source_dir = File.get_dir(tmp_dir, title = archive_url)

      Isabelle_System.extract(archive_path, component_dir.src, strip = true)


      /* build */

      progress.echo("Building rsync for " + platform_name + " ...")

      val build_script = List("./configure " + Bash.strings(build_options.sorted), "make")
      Isabelle_System.bash(build_script.mkString(" && "), cwd = source_dir.file,
        progress_stdout = progress.echo(_, verbose = true),
        progress_stderr = progress.echo(_, verbose = true)).check


      /* install */

      Isabelle_System.copy_file(source_dir + Path.explode("COPYING"), component_dir.LICENSE)
      Isabelle_System.copy_file(source_dir + Path.explode("rsync").platform_exe, platform_dir)


      /* settings */

      component_dir.write_settings("""
ISABELLE_RSYNC_HOME="$COMPONENT"
ISABELLE_RSYNC="$ISABELLE_RSYNC_HOME/platform_${ISABELLE_PLATFORM64}/rsync"
""")


      /* README */

      File.write(component_dir.README,
        "This is rsync " + version + " from " + download_url + """

The distribution has been built like this:

""" + ("cd src" :: build_script).map(s => "  " + s + "\n").mkString + """
See also:
  * https://github.com/WayneD/rsync
  * https://rsync.samba.org


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
    }
}


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_rsync", "build rsync component from source distribution",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var build_options = default_build_options
        var version = default_version
        var download_url = default_download_url
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle component_rsync [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -O OPT       add build option
    -R OPT       remove build option
    -U URL       download URL
                 (default: """" + default_download_url + """")
    -V VERSION   version (default: """ + default_version + """)
    -v           verbose

  Build rsync component from the specified source distribution.

  The default build options (for ./configure) are:
""" + default_build_options.map(opt => "    " + opt + "\n").mkString,
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "O:" -> (arg => build_options = Library.insert(arg)(build_options)),
          "R:" -> (arg => build_options = Library.remove(arg)(build_options)),
          "U:" -> (arg => download_url = arg),
          "V:" -> (arg => version = arg),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress(verbose = verbose)

        build_rsync(version = version, download_url = download_url, progress = progress,
          target_dir = target_dir, build_options = build_options)
      })
}
