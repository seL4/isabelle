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

  val default_hol_light_patched_url = "https://gitlab.inria.fr/hol-light-isabelle/hol-light.git"
  val default_hol_light_patched_rev = "master"

  val default_import_url = "https://gitlab.inria.fr/hol-light-isabelle/import.git"
  val default_import_rev = "master"

  def hol_light_dirs(base_dir: Path): (Path, Path) =
    (base_dir + Path.basic("hol-light"), base_dir + Path.basic("hol-light-patched"))

  val patched_files: List[Path] =
    List("fusion.ml", "statements.ml", "stage1.ml", "stage2.ml").map(Path.explode)

  def make_patch(base_dir: Path): String = {
    val (dir1, dir2) = hol_light_dirs(Path.current)
    (for (path <- patched_files) yield {
      val path1 = dir1 + path
      val path2 = dir2 + path
      if ((base_dir + path1).is_file || (base_dir + path2).is_file) {
        Isabelle_System.make_patch(base_dir, path1, path2)
      }
      else ""
    }).mkString
  }

  def build_hol_light_import(
    only_offline: Boolean = false,
    progress: Progress = new Progress,
    target_dir: Path = Path.current,
    hol_light_url: String = default_hol_light_url,
    hol_light_rev: String = default_hol_light_rev,
    hol_light_patched_url: String = default_hol_light_patched_url,
    hol_light_patched_rev: String = default_hol_light_patched_rev,
    import_url: String = default_import_url,
    import_rev: String = default_import_rev
  ): Unit = {
    /* system */

    if (!only_offline) {
      Linux.check_system()
      Isabelle_System.require_command("buffer", test = "-i /dev/null")
      Isabelle_System.require_command("patch")
    }


    /* component */

    val component_name = "hol_light_import-" + Date.Format.alt_date(Date.now())
    val component_dir = Components.Directory(target_dir + Path.basic(component_name)).create()

    val platform = Isabelle_Platform.self.ISABELLE_PLATFORM(windows = true, apple = true)
    val platform_dir = Isabelle_System.make_directory(component_dir.path + Path.basic(platform))


    /* settings */

    component_dir.write_settings("""
HOL_LIGHT_IMPORT="$COMPONENT"
HOL_LIGTH_BUNDLE="$HOL_LIGHT_IMPORT/bundle/proofs"
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
has been patched in 2 stages. The overall export process works like this:

  make

  patch -p1 < patches/stage1.patch
  ./ocaml-hol -I +compiler-libs stage1.ml

  patch -p1 < patches/stage2.patch
  export MAXTMS=10000
  ./ocaml-hol -I +compiler-libs stage2.ml

  gzip -d proofs.gz
  > maps.lst
  x86_64-linux/offline


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


      /* repository clones */

      val (hol_light_dir, hol_light_patched_dir) = hol_light_dirs(tmp_dir)
      val import_dir = tmp_dir + Path.basic("import")

      if (!only_offline) {
        Isabelle_System.git_clone(hol_light_url, hol_light_dir, checkout = hol_light_rev,
          progress = progress)

        Isabelle_System.git_clone(
          hol_light_patched_url, hol_light_patched_dir, checkout = hol_light_patched_rev,
          progress = progress)
      }

      Isabelle_System.git_clone(import_url, import_dir, checkout = import_rev, progress = progress)


      /* "offline" tool */

      progress.echo("Building offline tool ...")

      val offline_path = Path.explode("offline")
      val offline_exe = offline_path.platform_exe
      val import_offline_dir = import_dir + offline_path

      Isabelle_System.copy_dir(import_offline_dir, component_dir.path)
      (component_dir.path + Path.explode("offline/.gitignore")).file.delete

      progress.bash("make", cwd = import_offline_dir, echo = progress.verbose).check
      Isabelle_System.copy_file(import_offline_dir + offline_exe, platform_dir + offline_exe)
      File.set_executable(platform_dir + offline_exe)


      if (!only_offline) {

        /* patches */

        progress.echo("Preparing patches ...")

        val patches_dir = Isabelle_System.make_directory(component_dir.path + Path.basic("patches"))
        val patch1 = patches_dir + Path.basic("stage1.patch")
        val patch2 = patches_dir + Path.basic("stage2.patch")

        Isabelle_System.bash("git reset --hard origin/stdlib/isabelle-export-base",
          cwd = hol_light_patched_dir).check

        File.write(patch1, make_patch(tmp_dir))

        Isabelle_System.bash("patch -p1 < " + File.bash_path(patch1), cwd = hol_light_dir).check

        Isabelle_System.bash("git reset --hard origin/stdlib/isabelle-export",
          cwd = hol_light_patched_dir).check

        File.write(patch2, make_patch(tmp_dir))


        /* export */

        progress.echo("Exporting proofs ...")
        progress.bash(
          Library.make_lines("set -e", opam_env,
            "make",
            "./ocaml-hol -I +compiler-libs stage1.ml",
            "patch -p1 < " + File.bash_path(patch2),
            "export MAXTMS=10000",
            "./ocaml-hol -I +compiler-libs stage2.ml",
            "gzip -d proofs.gz",
            "> maps.lst",
            File.bash_path(platform_dir + offline_exe) + " proofs"
          ),
          cwd = hol_light_dir, echo = progress.verbose).check

        val bundle_dir = Isabelle_System.make_directory(component_dir.path + Path.explode("bundle"))
        Isabelle_System.copy_file(hol_light_dir + Path.explode("proofs"), bundle_dir)
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
        var hol_light_patched_url = default_hol_light_patched_url
        var hol_light_rev = default_hol_light_rev
        var hol_light_patched_rev = default_hol_light_patched_rev
        var import_url = default_import_url
        var import_rev = default_import_rev
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle component_hol_light_import [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -O           only build the "offline" tool
    -U URL       git URL for original HOL Light repository, default:
                 """ + default_hol_light_url + """
    -V URL       git URL for patched HOL Light repository, default:
                 """ + default_hol_light_patched_url + """
    -W URL       git URL for import repository, default:
                 """ + default_import_url + """
    -r REV       revision or branch to checkout HOL Light (default: """ +
                    default_hol_light_rev + """)
    -s REV       revision or branch to checkout HOL-Light-to-Isabelle (default: """ +
                    default_hol_light_patched_rev + """)
    -t REV       revision or branch to checkout import (default: """ +
                    default_import_rev + """)
    -v           verbose

  Build Isabelle component for HOL Light import.
""",
          "D:" -> (arg => target_dir = Path.explode(arg)),
          "O" -> (_ => only_offline = true),
          "U:" -> (arg => hol_light_url = arg),
          "V:" -> (arg => hol_light_patched_url = arg),
          "W:" -> (arg => import_url = arg),
          "r:" -> (arg => hol_light_rev = arg),
          "s:" -> (arg => hol_light_patched_rev = arg),
          "t:" -> (arg => import_rev = arg),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        if (more_args.nonEmpty) getopts.usage()

        val progress = new Console_Progress(verbose = verbose)

        build_hol_light_import(
          only_offline = only_offline, progress = progress, target_dir = target_dir,
          hol_light_url = hol_light_url,
          hol_light_rev = hol_light_rev,
          hol_light_patched_url = hol_light_patched_url,
          hol_light_patched_rev = hol_light_patched_rev,
          import_url = import_url,
          import_rev = import_rev)
      })
}
