/*  Title:      Pure/Admin/sync_repos.scala
    Author:     Makarius

Synchronize Isabelle + AFP repositories.
*/

package isabelle


object Sync_Repos {
  def sync_repos(target: String,
    progress: Progress = new Progress,
    port: Int = SSH.default_port,
    verbose: Boolean = false,
    thorough: Boolean = false,
    preserve_jars: Boolean = false,
    dry_run: Boolean = false,
    clean: Boolean = false,
    rev: String = "",
    afp_root: Option[Path] = None,
    afp_rev: String = ""
  ): Unit = {
    val target_dir = if (target.endsWith(":") || target.endsWith("/")) target else target + "/"

    val hg = Mercurial.self_repository()
    val afp_hg = afp_root.map(Mercurial.repository(_))

    val more_filter = if (preserve_jars) List("include *.jar", "protect *.jar") else Nil

    def sync(hg: Mercurial.Repository, dest: String, r: String, filter: List[String] = Nil): Unit =
      hg.sync(dest, rev = r, progress = progress, port = port, verbose = verbose,
        thorough = thorough, dry_run = dry_run, clean = clean, filter = filter ::: more_filter)

    progress.echo("\n* Isabelle repository:")
    sync(hg, target, rev, filter = List("protect /AFP", "protect /etc/ISABELLE_ID"))

    if (!dry_run) {
      Isabelle_System.with_tmp_dir("sync") { tmp_dir =>
        val id_path = tmp_dir + Path.explode("ISABELLE_ID")
        File.write(id_path, hg.id(rev = rev))
        Isabelle_System.rsync(port = port, thorough = thorough,
          args = List(File.standard_path(id_path), target_dir + "etc/"))
      }
    }

    for (hg <- afp_hg) {
      progress.echo("\n* AFP repository:")
      sync(hg, target_dir + "AFP", afp_rev)
    }
  }

  val isabelle_tool =
    Isabelle_Tool("sync_repos", "synchronize Isabelle + AFP repositories",
      Scala_Project.here, { args =>
        var afp_root: Option[Path] = None
        var clean = false
        var preserve_jars = false
        var thorough = false
        var afp_rev = ""
        var dry_run = false
        var rev = ""
        var port = SSH.default_port
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle sync_repos [OPTIONS] TARGET

  Options are:
    -A ROOT      include AFP with given root directory (":" for """ + AFP.BASE.implode + """)
    -J           preserve *.jar files
    -C           clean all unknown/ignored files on target
                 (implies -n for testing; use option -f to confirm)
    -T           thorough treatment of file content and directory times
    -a REV       explicit AFP revision (default: state of working directory)
    -f           force changes: no dry-run
    -n           no changes: dry-run
    -r REV       explicit revision (default: state of working directory)
    -p PORT      explicit SSH port (default: """ + SSH.default_port + """)
    -v           verbose

  Synchronize Isabelle + AFP repositories; see also "isabelle hg_sync".

  Examples (without -f as "dry-run"):

   * quick testing

      isabelle sync_repos -A: -J -C testmachine:test/isabelle_afp

   * accurate testing

      isabelle sync_repos -A: -T -C testmachine:test/isabelle_afp
""",
          "A:" -> (arg => afp_root = Some(if (arg == ":") AFP.BASE else Path.explode(arg))),
          "J" -> (_ => preserve_jars = true),
          "C" -> { _ => clean = true; dry_run = true },
          "T" -> (_ => thorough = true),
          "a:" -> (arg => afp_rev = arg),
          "f" -> (_ => dry_run = false),
          "n" -> (_ => dry_run = true),
          "r:" -> (arg => rev = arg),
          "p:" -> (arg => port = Value.Int.parse(arg)),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        val target =
          more_args match {
            case List(target) => target
            case _ => getopts.usage()
          }

        val progress = new Console_Progress
        sync_repos(target, progress = progress, port = port, verbose = verbose, thorough = thorough,
          preserve_jars = preserve_jars, dry_run = dry_run, clean = clean, rev = rev,
          afp_root = afp_root, afp_rev = afp_rev)
      }
    )
}
