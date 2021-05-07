/*  Title:      Pure/Admin/build_spass.scala
    Author:     Makarius

Build Isabelle SPASS component from unofficial download.
*/

package isabelle


object Build_SPASS
{
  /* build SPASS */

  val default_download_url = "https://www.cs.vu.nl/~jbe248/spass-3.8ds-src.tar.gz"
  val standard_version = "3.8ds"

  def build_spass(
    download_url: String = default_download_url,
    verbose: Boolean = false,
    progress: Progress = new Progress,
    target_dir: Path = Path.current): Unit =
  {
    Isabelle_System.with_tmp_dir("build")(tmp_dir =>
    {
      Isabelle_System.require_command("bison")
      Isabelle_System.require_command("flex")


      /* component */

      val Archive_Name = """^.*?([^/]+)$""".r
      val Component_Name = """^(.+)-src\.tar.gz$""".r
      val Version = """^[^-]+-([^-]+)$""".r

      val (archive_name, archive_base_name) =
        download_url match {
          case Archive_Name(name) => (name, Library.perhaps_unsuffix(".tar.gz", name))
          case _ => error("Failed to determine source archive name from " + quote(download_url))
        }

      val component_name =
        archive_name match {
          case Component_Name(name) => name
          case _ => error("Failed to determine component name from " + quote(archive_name))
        }

      val version =
        component_name match {
          case Version(version) => version
          case _ => error("Failed to determine component version from " + quote(component_name))
        }

      if (version != standard_version) {
        progress.echo_warning("Odd SPASS version " + version + " (expected " + standard_version + ")")
      }

      val component_dir = Isabelle_System.new_directory(target_dir + Path.basic(component_name))
      progress.echo("Component " + component_dir)

      val platform_name =
        proper_string(Isabelle_System.getenv("ISABELLE_PLATFORM64"))
          .getOrElse(error("No 64bit platform"))

      val platform_dir = Isabelle_System.make_directory(component_dir + Path.basic(platform_name))


      /* download source */

      val archive_path = tmp_dir + Path.basic(archive_name)
      Isabelle_System.download_file(download_url, archive_path, progress = progress)

      Isabelle_System.bash("tar xzf " + archive_path, cwd = tmp_dir.file).check
      Isabelle_System.bash(
        "tar xzf " + archive_path + " && mv " + Bash.string(archive_base_name) + " src",
        cwd = component_dir.file).check


      /* build */

      progress.echo("Building SPASS for " + platform_name + " ...")

      val build_dir = tmp_dir + Path.basic(archive_base_name)

      if (Platform.is_windows) {
        File.change(build_dir + Path.basic("misc.c"),
          _.replace("""#include "execinfo.h" """, "")
           .replaceAll("""void misc_DumpCore\(void\)[^}]+}""", "void misc_DumpCore(void) { abort(); }"))
      }

      Isabelle_System.bash("make",
        cwd = build_dir.file,
        progress_stdout = progress.echo_if(verbose, _),
        progress_stderr = progress.echo_if(verbose, _)).check


      /* install */

      Isabelle_System.copy_file(build_dir + Path.basic("LICENCE"),
        component_dir + Path.basic("LICENSE"))

      val install_files = List("SPASS")
      for (name <- install_files ::: install_files.map(_ + ".exe")) {
        val path = build_dir + Path.basic(name)
        if (path.is_file) Isabelle_System.copy_file(path, platform_dir)
      }


      /* settings */

      val etc_dir = Isabelle_System.make_directory(component_dir + Path.basic("etc"))
      File.write(etc_dir + Path.basic("settings"),
        """# -*- shell-script -*- :mode=shellscript:

SPASS_HOME="$COMPONENT/$ISABELLE_PLATFORM64"
SPASS_VERSION=""" + quote(version) + """
""")

      /* README */

      File.write(component_dir + Path.basic("README"),
"""This distribution of SPASS 3.8ds, described in Blanchette, Popescu, Wand, and
Weidenbach's ITP 2012 paper "More SPASS with Isabelle", has been compiled from
sources available at """ + download_url + """
via "make".

The Windows/Cygwin compilation required commenting out the line

    #include "execinfo.h"

in "misc.c" as well as most of the body of the "misc_DumpCore" function.

The latest official SPASS sources can be downloaded from
http://www.spass-prover.org/. Be aware, however, that the official SPASS
releases are not compatible with Isabelle.


Viel SPASS!


        Jasmin Blanchette
        16-May-2018

        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
    })
}

  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_spass", "build prover component from source distribution",
      Scala_Project.here, args =>
    {
      var target_dir = Path.current
      var download_url = default_download_url
      var verbose = false

      val getopts = Getopts("""
Usage: isabelle build_spass [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL
                 (default: """" + default_download_url + """")
    -v           verbose

  Build prover component from the specified source distribution.
""",
        "D:" -> (arg => target_dir = Path.explode(arg)),
        "U:" -> (arg => download_url = arg),
        "v" -> (_ => verbose = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress()

      build_spass(download_url = download_url, verbose = verbose, progress = progress,
        target_dir = target_dir)
    })
}
