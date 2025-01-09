/*  Title:      Pure/Admin/component_cygwin.scala
    Author:     Makarius

Produce pre-canned Cygwin distribution for Isabelle.
*/

package isabelle


object Component_Cygwin {
  val default_mirror: String = "https://isabelle.sketis.net/cygwin_2025"

  val packages: List[String] = List("curl", "libgmp-devel", "nano", "openssh", "perl")

  def build_cygwin(
    target_dir: Path = Path.current,
    mirror: String = default_mirror,
    more_packages: List[String] = Nil,
    progress: Progress = new Progress
  ): Unit = {
    require(Platform.is_windows, "Windows platform expected")

    Isabelle_System.with_tmp_dir("cygwin") { tmp_dir =>
      val cygwin = tmp_dir + Path.explode("cygwin")
      val cygwin_etc = cygwin + Path.explode("etc")
      val cygwin_isabelle = Isabelle_System.make_directory(cygwin + Path.explode("isabelle"))

      val cygwin_exe_name = mirror + "/setup-x86_64.exe"
      val cygwin_exe = cygwin_isabelle + Path.explode("cygwin.exe")
      Bytes.write(cygwin_exe,
        try { Bytes.read_url(cygwin_exe_name) }
        catch { case ERROR(_) => error("Failed to download " + quote(cygwin_exe_name)) })

      File.write(cygwin_isabelle + Path.explode("cygwin_mirror"), mirror)

      File.set_executable(cygwin_exe)
      Isabelle_System.bash(File.bash_path(cygwin_exe) + " -h </dev/null >/dev/null").check

      val res =
        progress.bash(
          File.bash_path(cygwin_exe) + " --site " + Bash.string(mirror) + " --no-verify" +
            " --local-package-dir 'C:\\temp'" +
            " --root " + File.bash_platform_path(cygwin) +
            " --packages " + quote((packages ::: more_packages).mkString(",")) +
            " --no-shortcuts --no-startmenu --no-desktop --quiet-mode",
          echo = true)
      if (!res.ok || !cygwin_etc.is_dir) error("Failed")

      for (name <- List("hosts", "protocols", "services", "networks", "passwd", "group"))
        (cygwin_etc + Path.explode(name)).file.delete

      (cygwin + Path.explode("Cygwin.bat")).file.delete

      Isabelle_System.bash("rm -f cygwin/usr/share/man/man1/:.1.gz", cwd = tmp_dir).check

      val archive =
        target_dir + Path.explode("cygwin-" + Date.Format.alt_date(Date.now()) + ".tar.gz")
      Isabelle_System.gnutar("-czf " + File.bash_path(archive) + " cygwin", dir = tmp_dir).check
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_cygwin", "produce pre-canned Cygwin distribution for Isabelle",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var mirror = default_mirror
        var more_packages: List[String] = Nil

        val getopts =
          Getopts("""
Usage: isabelle component_cygwin [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -R MIRROR    Cygwin mirror site (default """ + quote(default_mirror) + """)
    -p NAME      additional Cygwin package

  Produce pre-canned Cygwin distribution for Isabelle: this requires
  Windows administrator mode.
""",
            "D:" -> (arg => target_dir = Path.explode(arg)),
            "R:" -> (arg => mirror = arg),
            "p:" -> (arg => more_packages ::= arg))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress()

        build_cygwin(target_dir = target_dir, mirror = mirror, more_packages = more_packages,
          progress = progress)
      })
}
