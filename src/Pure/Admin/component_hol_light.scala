/*  Title:      Pure/Admin/component_hol_light.scala
    Author:     Makarius

Build component for HOL-Light, with export of facts and proofs, offline
optimization, and import to Isabelle/HOL.
*/

package isabelle


object Component_HOL_Light {
  /* resources */

  val default_hol_light_url = "https://github.com/jrh13/hol-light.git"
  val default_hol_light_rev = "Release-3.0.0"

  val hol_import_dir: Path = Path.explode("~~/src/HOL/Import")

  def build_hol_light_import(
    only_offline: Boolean = false,
    progress: Progress = new Progress,
    target_dir: Path = Path.current,
    hol_light_url: String = default_hol_light_url,
    hol_light_rev: String = default_hol_light_rev
  ): Unit = {
    /* system */

    if (!only_offline) {
      Linux.check_system()
      Isabelle_System.require_command("patch")
      Isabelle_System.require_command("zstd")
    }


    /* component */

    val component_name = "hol_light_import-" + Date.Format.alt_date(Date.now())
    val component_dir = Components.Directory(target_dir + Path.basic(component_name)).create()

    val platform = Isabelle_Platform.self.ISABELLE_PLATFORM(windows = true, apple = true)
    val platform_dir = Isabelle_System.make_directory(component_dir.path + Path.basic(platform))


    /* settings */

    component_dir.write_settings("""
HOL_LIGHT_IMPORT="$COMPONENT"
HOL_LIGHT_BUNDLE="$HOL_LIGHT_IMPORT/bundle/proofs.zst"
HOL_LIGHT_OFFLINE="$HOL_LIGHT_IMPORT/${ISABELLE_WINDOWS_PLATFORM64:-${ISABELLE_APPLE_PLATFORM64:-$ISABELLE_PLATFORM64}}/offline"
""")


    /* README */

    File.write(component_dir.README,
      """Author: Cezary Kaliszyk, University of Innsbruck, 2013
Author: Alexander Krauss, QAware GmbH, 2013
Author: Sophie Tourret, INRIA, 2024
Author: Stéphane Glondu, INRIA, 2024

LICENSE (export tools): BSD-3 from Isabelle
LICENSE (HOL Light proofs): BSD-2 from HOL Light


This is an export of primitive proofs from HOL Light """ + hol_light_rev + """.

The original repository """ + hol_light_url + """
has been patched in 2 phases. The overall export process works like this:

  cd hol-light
  make

  patch -p1 < "$HOL_LIGHT_IMPORT/patches/patch1"
  ./ocaml-hol -I +compiler-libs stage1.ml

  patch -p1 < "$HOL_LIGHT_IMPORT/patches/patch2"
  export MAXTMS=10000
  ./ocaml-hol -I +compiler-libs stage2.ml

  > maps.lst
  "$HOL_LIGHT_IMPORT/x86_64-linux/offline"


      Makarius
      """ + Date.Format.date(Date.now()) + "\n")


    Isabelle_System.with_tmp_dir("build") { tmp_dir =>

      /* OCaml setup */

      progress.echo("Setup OCaml ...")
      progress.bash(
        if (only_offline) "isabelle ocaml_setup_base"
        else "isabelle ocaml_setup && isabelle ocaml_opam install -y camlp5",
        echo = progress.verbose).check

      val opam_env = Isabelle_System.bash("isabelle ocaml_opam env").check.out


      /* "offline" tool */

      progress.echo("Building offline tool ...")

      val offline_path = Path.explode("offline")
      val offline_exe = offline_path.platform_exe
      val offline_dir = Isabelle_System.make_directory(tmp_dir + offline_path)

      Isabelle_System.copy_dir(hol_import_dir + offline_path, offline_dir, direct = true)

      progress.bash("ocamlopt offline.ml -o offline",
        cwd = offline_dir, echo = progress.verbose).check
      Isabelle_System.copy_file(offline_dir + offline_exe, platform_dir + offline_exe)
      File.set_executable(platform_dir + offline_exe)


      if (!only_offline) {
        /* clone repository */

        val hol_light_dir = tmp_dir + Path.basic("hol-light")
        Isabelle_System.git_clone(hol_light_url, hol_light_dir, checkout = hol_light_rev,
          progress = progress)


        /* patches */

        Isabelle_System.make_directory(component_dir.path + Path.basic("patches"))

        def patch(n: Int, source: Boolean = false): Path =
          (if (source) hol_import_dir else component_dir.path) + Path.explode("patches/patch" + n)

        for (n <- List(1, 2)) Isabelle_System.copy_file(patch(n, source = true), patch(n))


        /* export stages */

        def run(n: Int, lines: String*): Unit = {
          val title = "stage " + n
          if (n > 0) progress.echo("Running " + title + " ...")

          val start = Time.now()
          progress.bash(cat_lines("set -e" :: opam_env :: lines.toList),
            cwd = hol_light_dir, echo = progress.verbose).check.timing
          val elapsed = Time.now() - start

          if (n > 0) {
            progress.echo("Finished " + title + " (" + elapsed.message_hms + " elapsed time)")
          }
        }

        run(0, "make")
        run(1,
          "patch -p1 < " + File.bash_path(patch(1)),
          "./ocaml-hol -I +compiler-libs stage1.ml")
        run(2,
          "patch -p1 < " + File.bash_path(patch(2)),
          "export MAXTMS=10000",
          "./ocaml-hol -I +compiler-libs stage2.ml")
        run(3,
          "> maps.lst",
          File.bash_path(platform_dir + offline_exe) + " proofs",
          "zstd -8 proofs")

        val bundle_dir = Isabelle_System.make_directory(component_dir.path + Path.explode("bundle"))
        Isabelle_System.copy_file(hol_light_dir + Path.explode("proofs.zst"), bundle_dir)
      }
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("component_hol_light_import", "build Isabelle component for HOL Light import",
      Scala_Project.here,
      { args =>
        var target_dir = Path.current
        var only_offline = false
        var hol_light_url = default_hol_light_url
        var hol_light_rev = default_hol_light_rev
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle component_hol_light_import [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -O           only build the "offline" tool
    -U URL       git URL for original HOL Light repository, default:
                 """ + default_hol_light_url + """
    -r REV       revision or branch to checkout HOL Light (default: """ +
                    default_hol_light_rev + """)
    -v           verbose

  Build Isabelle component for HOL Light import.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "O" -> (_ => only_offline = true),
          "U:" -> (arg => hol_light_url = arg),
          "r:" -> (arg => hol_light_rev = arg),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress(verbose = verbose)

        build_hol_light_import(
          only_offline = only_offline, progress = progress, target_dir = target_dir,
          hol_light_url = hol_light_url, hol_light_rev = hol_light_rev)
      })
}
