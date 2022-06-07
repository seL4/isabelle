/*  Title:      Pure/Admin/sync_repos.scala
    Author:     Makarius

Synchronize Isabelle + AFP repositories.
*/

package isabelle


object Sync_Repos {
  def sync_repos(context: Rsync.Context, target: String,
    verbose: Boolean = false,
    thorough: Boolean = false,
    preserve_jars: Boolean = false,
    dry_run: Boolean = false,
    rev: String = "",
    afp_root: Option[Path] = None,
    afp_rev: String = ""
  ): Unit = {
    val hg = Mercurial.self_repository()
    val afp_hg = afp_root.map(Mercurial.repository(_))

    val more_filter = if (preserve_jars) List("include *.jar", "protect *.jar") else Nil

    def sync(hg: Mercurial.Repository, dest: String, r: String,
      contents: List[File.Content] = Nil, filter: List[String] = Nil
    ): Unit = {
      hg.sync(context, dest, rev = r, verbose = verbose, thorough = thorough, dry_run = dry_run,
        contents = contents, filter = filter ::: more_filter)
    }

    context.progress.echo_if(verbose, "\n* Isabelle repository:")
    sync(hg, target, rev,
      contents = List(File.Content(Path.explode("etc/ISABELLE_ID"), hg.id(rev = rev))),
      filter = List("protect /AFP"))

    for (hg <- afp_hg) {
      context.progress.echo_if(verbose, "\n* AFP repository:")
      sync(hg, Rsync.append(target, "AFP"), afp_rev)
    }
  }

  val isabelle_tool =
    Isabelle_Tool("sync_repos", "synchronize Isabelle + AFP repositories",
      Scala_Project.here, { args =>
        var afp_root: Option[Path] = None
        var preserve_jars = false
        var protect_args = false
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
    -S           robust (but less portable) treatment of spaces in directory names
    -T           thorough treatment of file content and directory times
    -a REV       explicit AFP revision (default: state of working directory)
    -n           no changes: dry-run
    -r REV       explicit revision (default: state of working directory)
    -p PORT      explicit SSH port (default: """ + SSH.default_port + """)
    -v           verbose

  Synchronize Isabelle + AFP repositories; see also "isabelle hg_sync".

  Example: quick testing

    isabelle sync_repos -A: -J testmachine:test/isabelle_afp

  Example: accurate testing

    isabelle sync_repos -A: -T testmachine:test/isabelle_afp
""",
          "A:" -> (arg => afp_root = Some(if (arg == ":") AFP.BASE else Path.explode(arg))),
          "J" -> (_ => preserve_jars = true),
          "S" -> (_ => protect_args = true),
          "T" -> (_ => thorough = true),
          "a:" -> (arg => afp_rev = arg),
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
        val context = Rsync.Context(progress, port = port, protect_args = protect_args)
        sync_repos(context, target, verbose = verbose, thorough = thorough,
          preserve_jars = preserve_jars, dry_run = dry_run, rev = rev, afp_root = afp_root,
          afp_rev = afp_rev)
      }
    )
}
