/*  Title:      Pure/Admin/build_e.scala
    Author:     Makarius

Build Isabelle E prover component from official downloads.
*/

package isabelle


object Build_E
{
  /* build E prover */

  val default_version = "2.5"

  val default_download_url =
    "https://wwwlehre.dhbw-stuttgart.de/~sschulz/WORK/E_DOWNLOAD"

  val default_runepar_url =
    "https://raw.githubusercontent.com/JUrban/MPTP2/66f03e5b6df8/MaLARea/bin/runepar.pl"

  def build_e(
    version: String = default_version,
    download_url: String = default_download_url,
    runepar_url: String = default_runepar_url,
    verbose: Boolean = false,
    progress: Progress = new Progress,
    target_dir: Path = Path.current)
  {
    Isabelle_System.with_tmp_dir("e")(tmp_dir =>
    {
      /* component */

      val component_name = "e-" + version
      val component_dir = target_dir + Path.basic(component_name)
      if (component_dir.is_dir) error("Component directory already exists: " + component_dir)
      else {
        progress.echo("Component " + component_dir)
        Isabelle_System.mkdirs(component_dir)
      }

      val platform_name =
        proper_string(Isabelle_System.getenv("ISABELLE_PLATFORM64"))
          .getOrElse(error("No 64bit platform"))

      val platform_dir = component_dir + Path.basic(platform_name)
      Isabelle_System.mkdirs(platform_dir)


      /* runepar.pl */

      val runepar_path = platform_dir + Path.basic("runepar.pl")
      Isabelle_System.download(runepar_url, runepar_path, progress = progress)

      File.write(runepar_path,
        File.read(runepar_path)
          .replace("#!/usr/bin/perl", "#!/usr/bin/env perl")
          .replace("bin/eprover", "$ENV{E_HOME}/eprover")
          .replace("bin/eproof", "$ENV{E_HOME}/eproof"))

      File.set_executable(runepar_path, true)


      /* download source */

      val e_url = download_url + "/V_" + version + "/E.tgz"
      val e_path = tmp_dir + Path.explode("E.tgz")
      Isabelle_System.download(e_url, e_path, progress = progress)

      Isabelle_System.bash("tar xzf " + e_path, cwd = tmp_dir.file).check
      Isabelle_System.bash("tar xzf " + e_path + " && mv E src", cwd = component_dir.file).check


      /* build */

      progress.echo("Building E prover ...")

      val build_dir = tmp_dir + Path.basic("E")
      val build_options =
      {
        val result = Isabelle_System.bash("./configure --help", cwd = build_dir.file)
        if (result.check.out.containsSlice("--enable-ho")) " --enable-ho" else ""
      }

      val build_script = "./configure" + build_options + " && make"
      Isabelle_System.bash(build_script,
        cwd = build_dir.file,
        progress_stdout = progress.echo_if(verbose, _),
        progress_stderr = progress.echo_if(verbose, _)).check


      /* install */

      File.copy(build_dir + Path.basic("COPYING"), component_dir + Path.basic("LICENSE"))

      val install_files = List("epclextract", "eproof_ram", "eprover", "eprover-ho")
      for (name <- install_files ::: install_files.map(_ + ".exe")) {
        val path = build_dir + Path.basic("PROVER") + Path.basic(name)
        if (path.is_file) File.copy(path, platform_dir)
      }
      Isabelle_System.bash("if [ -f eprover-ho ]; then mv eprover-ho eprover; fi",
        cwd = platform_dir.file).check

      val eproof_ram = platform_dir + Path.basic("eproof_ram")
      if (eproof_ram.is_file) {
        File.write(eproof_ram,
          File.read(eproof_ram)
            .replace("EXECPATH=.", "EXECPATH=`dirname \"$0\"`"))
      }


      /* settings */

      val etc_dir = component_dir + Path.basic("etc")
      Isabelle_System.mkdirs(etc_dir)
      File.write(etc_dir + Path.basic("settings"),
        """# -*- shell-script -*- :mode=shellscript:

E_HOME="$COMPONENT/$ISABELLE_PLATFORM64"
E_VERSION=""" + quote(version) + """
""")

      /* README */

      File.write(component_dir + Path.basic("README"),
        "This is E prover " + version + " from\n" + e_url + """

The distribution has been built like this:

    cd src && """ + build_script + """

Only a few executables from PROVERS/ have been moved to the platform-specific
Isabelle component directory: x86_64-linux etc.

This includes a copy of Josef Urban's "runepar.pl" script, modified to use
the correct path.


    Makarius
    """ + Date.Format.date(Date.now()) + "\n")
    })
}

  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_e", "build Isabelle E prover component from official download",
    args =>
    {
      var download_url = default_download_url
      var target_dir = Path.current
      var runepar_url = default_runepar_url
      var version = default_version
      var verbose = false

      val getopts = Getopts("""
Usage: isabelle build_e [OPTIONS] DOWNLOAD

  Options are:
    -E URL       E prover download URL
                 (default: """ + default_download_url + """)
    -D DIR       target directory (default ".")
    -R URL       URL for runepar.pl by Josef Urban
                 (default: """ + default_runepar_url + """)
    -V VERSION   E prover version (default: """ + default_version + """)
    -v           verbose

  Build E prover component from the specified download URLs and version.
""",
        "E:" -> (arg => download_url = arg),
        "D:" -> (arg => target_dir = Path.explode(arg)),
        "R:" -> (arg => runepar_url = arg),
        "V:" -> (arg => version = arg),
        "v" -> (_ => verbose = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress()

      build_e(version = version, download_url = download_url, runepar_url = runepar_url,
        verbose = verbose, progress = progress, target_dir = target_dir)
    })
}
