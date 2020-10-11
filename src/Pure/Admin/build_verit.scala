/*  Title:      Pure/Admin/build_csdp.scala
    Author:     Makarius

Build Isabelle veriT component from official download.
*/

package isabelle


object Build_VeriT
{
  val default_download_url = "https://verit.loria.fr/distrib/veriT-stable2016.tar.gz"


  /* flags */

  sealed case class Flags(platform: String, configure: String = "")
  {
    def print: Option[String] =
      if (configure.isEmpty) None
      else Some("  * " + platform + ":\n    ./configure " + configure)
  }

  val build_flags: List[Flags] =
    List(
      Flags("arm64-linux", configure = "--enable-static"),
      Flags("x86_64-linux", configure = "--enable-static"),
      Flags("x86_64-darwin"),
      Flags("x86_64-cygwin"))


  /* build veriT */

  def build_verit(
    download_url: String = default_download_url,
    verbose: Boolean = false,
    progress: Progress = new Progress,
    target_dir: Path = Path.current)
  {
    Isabelle_System.with_tmp_dir("build")(tmp_dir =>
    {
      /* required commands */

      List("autoconf", "bison", "flex").foreach(cmd =>
        if (!Isabelle_System.bash(cmd + " --version").ok) error("Missing command: " + cmd))


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

      val platform_build_flags =
        build_flags.find(flags => flags.platform == platform_name) match {
          case None => error("No build flags for platform " + quote(platform_name))
          case Some(flags) => flags
        }

      val build_script =
"""
  set -e
  autoconf
  ./configure """ + platform_build_flags.configure + """
  make
"""
      progress.bash(build_script, cwd = build_dir.file, echo = verbose).check


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

    autoconf && ./configure && make

Some platforms require specific flags as follows:

""" + build_flags.flatMap(_.print).mkString("\n\n") + """


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
