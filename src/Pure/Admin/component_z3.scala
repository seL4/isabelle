/*  Title:      Pure/Admin/component_z3.scala
    Author:     Makarius

Build Isabelle Z3 component from sources, with minimal patches.
*/

package isabelle


object Component_Z3 {
  /* build z3 */

  val default_download_url = "https://github.com/Z3Prover/z3/archive/0482e7fe727c75e259ac55a932b28cf1842c530e.tar.gz"

  val build_patch = """diff -Nru z3-orig/scripts/mk_util.py z3/scripts/mk_util.py
--- z3-orig/scripts/mk_util.py  2015-03-25 19:46:28.000000000 +0100
+++ z3/scripts/mk_util.py       2026-09-28 15:02:43.849271508 +0200
@@ -1784,7 +1784,7 @@
         if GIT_HASH:
             CPPFLAGS = '%s -DZ3GITHASH=%s' % (CPPFLAGS, GIT_HASH)
         CXXFLAGS = '%s -fvisibility=hidden -c' % CXXFLAGS
-        HAS_OMP = test_openmp(CXX)
+        HAS_OMP = False
         if HAS_OMP:
             CXXFLAGS = '%s -fopenmp -mfpmath=sse' % CXXFLAGS
             LDFLAGS  = '%s -fopenmp' % LDFLAGS
@@ -1839,7 +1839,7 @@
             CPPFLAGS     = '%s -DZ3DEBUG' % CPPFLAGS
         if TRACE or DEBUG_MODE:
             CPPFLAGS     = '%s -D_TRACE' % CPPFLAGS
-        CXXFLAGS         = '%s -msse -msse2' % CXXFLAGS
+        CXXFLAGS         = '%s -msse -msse2 -std=c++03' % CXXFLAGS
         config.write('PREFIX=%s\n' % PREFIX)
         config.write('CC=%s\n' % CC)
         config.write('CXX=%s\n' % CXX)
"""
  val build_script = "env CC=clang CXX=clang++ python2 scripts/mk_make.py && make -C build"

  def build_z3(
    download_url: String = default_download_url,
    progress: Progress = new Progress,
    target_dir: Path = Path.current
  ): Unit = {
    Isabelle_System.with_tmp_dir("build") { build_dir =>
      Isabelle_System.require_patch()
      Isabelle_System.require_command("clang")
      Isabelle_System.require_command("clang++")
      Isabelle_System.require_command("make")
      Isabelle_System.require_command("python2")


      /* component */

      val component_date = Date.Format.alt_date(Date.now())
      val component_name = "z3-" + component_date
      val component_dir =
        Components.Directory(target_dir + Path.basic(component_name)).create(progress = progress)


      /* platform */

      val platform = Isabelle_Platform.local
      val platform_name = platform.ISABELLE_PLATFORM(windows = true, apple = true)
      val platform_dir =
        Isabelle_System.make_directory(component_dir.path + Path.basic(platform_name))


      /* download and patch sources */

      val archive_name =
        Url.get_base_name(download_url).getOrElse(error("No base name in " + quote(download_url)))
      val archive = build_dir + Path.basic(archive_name)
      Isabelle_System.download_file(download_url, archive, progress = progress)
      Isabelle_System.extract(archive, build_dir, strip = true)

      Isabelle_System.apply_patch(build_dir, build_patch, progress = progress)

      if (platform.is_arm) {
        File.change(build_dir + Path.explode("scripts/mk_util.py"), strict = true) {
          _.replacing("-msse -msse2" -> "")
        }
      }


      /* build */

      progress.echo("Building Z3 for " + platform_name + " ...")

      progress.bash(build_script, cwd = build_dir, echo = progress.verbose).check

      Isabelle_System.copy_file(build_dir + Path.explode("build/z3").platform_exe, platform_dir)
      Isabelle_System.copy_file(build_dir + Path.explode("LICENSE.txt"), component_dir.path)


      /* settings */

      component_dir.write_settings("""
Z3_HOME="$COMPONENT/${ISABELLE_WINDOWS_PLATFORM32:-${ISABELLE_APPLE_PLATFORM64:-$ISABELLE_PLATFORM64}}"
Z3_VERSION="4.4.0pre"

Z3_SOLVER="$Z3_HOME/z3"

if [ -e "$Z3_HOME" ]
then
  Z3_INSTALLED="yes"
fi
""")


      /* README */

      File.write(component_dir.README,
"""This Isabelle component provides old z3 4.4.0 pre-release (revision 0482e7fe727c),
as required for Isabelle/HOL proof reconstruction in the "smt" proof method.

For Windows, the executable was a download z3-4.4.0.0482e7fe727c-x86-win.zip
from the former website http://z3.codeplex.com/releases (16-May-2018).

For Linux and macOS, the binaries have been built from sources
""" + download_url + """
with the following patch (without "-msse -msse2" on ARM64):

""" + build_patch + """
using the build command-line: """ + build_script + """


        Makarius
        """ + Date.Format.date(Date.now()) + "\n")
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_z3", "build prover component from sources", Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var download_url = default_download_url
        var component_name = ""
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle component_z3 [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       download URL
                 (default: """" + default_download_url + """")
    -v           verbose

  Build prover component from official sources.

  Linux prerequisites:
    - Ubuntu 20.04 LTS
    - apt packages:
      apt-get update && apt-get upgrade -y && apt autoremove -y
      apt install -y curl less libfontconfig1 libgomp1 clang make patch python2

  macOS prerequisites:
    - macOS 13 Ventura
    - Xcode command-line tools, notably /usr/bin/clang
    - Python 2, e.g. https://www.python.org/downloads/release/python-2718

  Windows prerequisites: not supported, use existing Z3 binaries
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "U:" -> (arg => download_url = arg),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress(verbose = verbose)

        build_z3(download_url = download_url, progress = progress, target_dir = target_dir)
      })
}
