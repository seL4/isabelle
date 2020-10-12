/*  Title:      Pure/Admin/build_csdp.scala
    Author:     Makarius

Build Isabelle veriT component from official download.
*/

package isabelle


object Build_VeriT
{
  val default_download_url = "https://verit.loria.fr/distrib/veriT-stable2016.tar.gz"


  /* build veriT */

  def build_verit(
    download_url: String = default_download_url,
    verbose: Boolean = false,
    progress: Progress = new Progress,
    target_dir: Path = Path.current)
  {
    Isabelle_System.with_tmp_dir("build")(tmp_dir =>
    {
      Isabelle_System.require_command("autoconf", "bison", "flex", "wget")


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

      val build_dir = tmp_dir + Path.basic(source_name)
      val build_script =
"""
    autoconf
    ./configure
    ln -s gmp-local extern/gmp
    make
"""
      progress.bash("set -e\n" + build_script, cwd = build_dir.file, echo = verbose).check


      /* install */

      File.copy(build_dir + Path.explode("LICENSE"), component_dir)
      File.copy(build_dir + Path.explode("veriT"), platform_dir)


      /* settings */

      val etc_dir = Isabelle_System.make_directory(component_dir + Path.basic("etc"))
      File.write(etc_dir + Path.basic("settings"),
        """# -*- shell-script -*- :mode=shellscript:

VERIT_HOME="$COMPONENT/$ISABELLE_PLATFORM64"
VERIT_VERSION=""" + quote(version) + """

VERIT_SOLVER="$VERIT_HOME/veriT"

if [ -e "$VERIT_HOME" ]
then
  VERIT_INSTALLED="yes"
fi
""")


      /* README */

      File.write(component_dir + Path.basic("README"),
"""This is veriT """ + version + """ from
""" + download_url + """

It has been built from sources like this:
""" + build_script + """

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
      var download_url = default_download_url
      var verbose = false

      val getopts = Getopts("""
Usage: isabelle build_verit [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL
                 (default: """" + default_download_url + """")
    -v           verbose

  Build prover component from official download.
""",
        "D:" -> (arg => target_dir = Path.explode(arg)),
        "U:" -> (arg => download_url = arg),
        "v" -> (_ => verbose = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress()

      build_verit(download_url = download_url, verbose = verbose, progress = progress,
        target_dir = target_dir)
    })
}
