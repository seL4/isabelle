/*  Title:      Pure/Admin/component_rsync.scala
    Author:     Makarius

Build Isabelle rsync component from official source distribution.
*/

package isabelle


object Component_Rsync {
  /* build rsync */

  val default_version = "3.2.7"
  val default_download_url = "https://github.com/WayneD/rsync/archive/refs/tags"
  val default_build_options =
    "--disable-openssl --disable-xxhash --disable-zstd --disable-lz4 --disable-md2man --disable-acl-support --disable-xattr-support"

  def build_rsync(
    version: String = default_version,
    download_url: String = default_download_url,
    progress: Progress = new Progress,
    target_dir: Path = Path.current,
    build_options: String = default_build_options
  ): Unit = {
    Isabelle_System.with_tmp_dir("build") { tmp_dir =>
      /* component */

      val component_name = "rsync-" + version
      val component_dir =
        Components.Directory(target_dir + Path.basic(component_name)).create(progress = progress)

      val platform_name =
        proper_string(Isabelle_System.getenv("ISABELLE_PLATFORM64"))
          .getOrElse(error("No 64bit platform"))

      val platform_dir =
        Isabelle_System.make_directory(component_dir.path + Path.basic(platform_name))


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

      val build_script = "./configure " + build_options + " && make"
      Isabelle_System.bash(build_script, cwd = source_dir.file,
        progress_stdout = progress.echo(_, verbose = true),
        progress_stderr = progress.echo(_, verbose = true)).check


      /* install */

      Isabelle_System.copy_file(source_dir + Path.explode("COPYING"), component_dir.LICENSE)
      Isabelle_System.copy_file(source_dir + Path.explode("rsync").platform_exe, platform_dir)


      /* settings */

      component_dir.write_settings("""
ISABELLE_RSYNC_HOME="$COMPONENT/$ISABELLE_PLATFORM64"
ISABELLE_RSYNC="$ISABELLE_RSYNC_HOME/rsync"
""")


      /* README */

      File.write(component_dir.README,
        "This is rsync " + version + " from " + download_url + """

See also:
  * https://github.com/WayneD/rsync
  * https://rsync.samba.org

The distribution has been built like this:

    cd src && """ + build_script + """


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
        var version = default_version
        var download_url = default_download_url
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle component_rsync [OPTIONS] [BUILD_OPTIONS ...]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL
                 (default: """" + default_download_url + """")
    -V VERSION   version (default: """ + default_version + """)
    -v           verbose

  Build rsync component from the specified source distribution. The default
  BUILD_OPTIONS are:

  """ + default_build_options + "\n",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => download_url = arg),
          "V:" -> (arg => version = arg),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        val build_options =
          if (more_args.isEmpty) default_build_options else Bash.strings(more_args)

        val progress = new Console_Progress(verbose = verbose)

        build_rsync(version = version, download_url = download_url, progress = progress,
          target_dir = target_dir, build_options = build_options)
      })
}
