/*  Title:      Pure/Admin/component_spass.scala
    Author:     Makarius

Build Isabelle SPASS component from unofficial download.
*/

package isabelle


object Component_SPASS {
  /* build SPASS */

  val default_download_url = "https://www.cs.vu.nl/~jbe248/spass-3.8ds-src.tar.gz"
  val standard_version = "3.8ds"

  def build_spass(
    download_url: String = default_download_url,
    progress: Progress = new Progress,
    target_dir: Path = Path.current
  ): Unit = {
    Isabelle_System.with_tmp_dir("build") { tmp_dir =>
      Isabelle_System.require_command("bison")
      Isabelle_System.require_command("flex")


      /* component */

      val Archive_Name = """^.*?([^/]+)$""".r
      val Component_Name = """^(.+)-src\.tar.gz$""".r
      val Version = """^[^-]+-([^-]+)$""".r

      val archive_name =
        download_url match {
          case Archive_Name(name) => name
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

      val component_dir =
        Components.Directory(target_dir + Path.basic(component_name)).create(progress = progress)

      val platform_name = Isabelle_Platform.local.ISABELLE_PLATFORM()
      val platform_dir =
        Isabelle_System.make_directory(component_dir.path + Path.basic(platform_name))


      /* download source */

      val archive_path = tmp_dir + Path.basic(archive_name)
      Isabelle_System.download_file(download_url, archive_path, progress = progress)

      Isabelle_System.extract(archive_path, tmp_dir)
      val source_dir = File.get_dir(tmp_dir, title = download_url)

      Isabelle_System.extract(archive_path, component_dir.src, strip = true)


      /* build */

      progress.echo("Building SPASS for " + platform_name + " ...")

      if (Platform.is_windows) {
        File.change(source_dir + Path.basic("misc.c")) {
          _.replace("""#include "execinfo.h" """, "")
           .replaceAll("""void misc_DumpCore\(void\)[^}]+}""", "void misc_DumpCore(void) { abort(); }")
        }
      }

      Isabelle_System.bash("make", cwd = source_dir,
        progress_stdout = progress.echo(_, verbose = true),
        progress_stderr = progress.echo(_, verbose = true)).check


      /* install */

      Isabelle_System.copy_file(source_dir + Path.basic("LICENCE"), component_dir.LICENSE)

      val install_files = List("SPASS")
      for (name <- install_files ::: install_files.map(_ + ".exe")) {
        val path = source_dir + Path.basic(name)
        if (path.is_file) Isabelle_System.copy_file(path, platform_dir)
      }


      /* settings */

      component_dir.write_settings("""
SPASS_HOME="$COMPONENT/$ISABELLE_PLATFORM64"
SPASS_VERSION=""" + quote(version) + """
""")


      /* README */

      File.write(component_dir.README,
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
    }
}


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_spass", "build prover component from source distribution",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var download_url = default_download_url
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle component_spass [OPTIONS]

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

        val progress = new Console_Progress(verbose = verbose)

        build_spass(download_url = download_url, progress = progress, target_dir = target_dir)
      })
}
