/*  Title:      Pure/Admin/build_csdp.scala
    Author:     Makarius

Build Isabelle veriT component from official download.
*/

package isabelle


object Build_VeriT
{
  val default_download_url = "https://verit.loria.fr/rmx/2020.10/verit-2020.10-rmx.tar.gz"


  /* build veriT */

  def build_verit(
    download_url: String = default_download_url,
    verbose: Boolean = false,
    progress: Progress = new Progress,
    target_dir: Path = Path.current,
    mingw: MinGW = MinGW.none)
  {
    mingw.check

    Isabelle_System.with_tmp_dir("build")(tmp_dir =>
    {
      /* component */

      val Archive_Name = """^.*?([^/]+)$""".r
      val Version = """^[^-]+-(.+)\.tar.gz$""".r

      val archive_name =
        download_url match {
          case Archive_Name(name) => name
          case _ => error("Failed to determine source archive name from " + quote(download_url))
        }

      val version =
        archive_name match {
          case Version(version) => version
          case _ => error("Failed to determine component version from " + quote(archive_name))
        }

      val component_name = "verit-" + version
      val component_dir = Isabelle_System.new_directory(target_dir + Path.basic(component_name))
      progress.echo("Component " + component_dir)


      /* platform */

      val platform_name =
        proper_string(Isabelle_System.getenv("ISABELLE_WINDOWS_PLATFORM64")) orElse
        proper_string(Isabelle_System.getenv("ISABELLE_PLATFORM64")) getOrElse
        error("No 64bit platform")

      val platform_dir = Isabelle_System.make_directory(component_dir + Path.basic(platform_name))


      /* download source */

      val archive_path = tmp_dir + Path.basic(archive_name)
      Isabelle_System.download(download_url, archive_path, progress = progress)

      Isabelle_System.bash("tar xzf " + File.bash_path(archive_path), cwd = tmp_dir.file).check
      val source_name = File.get_dir(tmp_dir)

      Isabelle_System.bash(
        "tar xzf " + archive_path + " && mv " + Bash.string(source_name) + " src",
        cwd = component_dir.file).check


      /* build */

      progress.echo("Building veriT for " + platform_name + " ...")

      val configure_options =
        if (Platform.is_linux) "LDFLAGS=-Wl,-rpath,_DUMMY_" else ""

      val build_dir = tmp_dir + Path.basic(source_name)
      progress.bash(mingw.bash_script("set -e\n./configure " + configure_options + "\nmake"),
        cwd = build_dir.file, echo = verbose).check


      /* install */

      File.copy(build_dir + Path.explode("LICENSE"), component_dir)

      val exe_path = Path.basic("veriT").platform_exe
      File.copy(build_dir + exe_path, platform_dir)
      Executable.libraries_closure(platform_dir + exe_path, filter = Set("libgmp"), mingw = mingw)


      /* settings */

      val etc_dir = Isabelle_System.make_directory(component_dir + Path.basic("etc"))
      File.write(etc_dir + Path.basic("settings"),
        """# -*- shell-script -*- :mode=shellscript:

ISABELLE_VERIT="$COMPONENT/${ISABELLE_WINDOWS_PLATFORM64:-$ISABELLE_PLATFORM64}/veriT"
""")


      /* README */

      File.write(component_dir + Path.basic("README"),
"""This is veriT """ + version + """ from
""" + download_url + """

It has been built from sources like this:

  cd src
  ./configure
  make


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
    })
}


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_verit", "build prover component from official download",
    args =>
    {
      var target_dir = Path.current
      var mingw = MinGW.none
      var download_url = default_download_url
      var verbose = false

      val getopts = Getopts("""
Usage: isabelle build_verit [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -M DIR       msys/mingw root specification for Windows
    -U URL       download URL
                 (default: """" + default_download_url + """")
    -v           verbose

  Build prover component from official download.
""",
        "D:" -> (arg => target_dir = Path.explode(arg)),
        "M:" -> (arg => mingw = MinGW(Path.explode(arg))),
        "U:" -> (arg => download_url = arg),
        "v" -> (_ => verbose = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress()

      build_verit(download_url = download_url, verbose = verbose, progress = progress,
        target_dir = target_dir, mingw = mingw)
    })
}
