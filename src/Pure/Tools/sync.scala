/*  Title:      Pure/Tools/sync.scala
    Author:     Makarius

Synchronize Isabelle + AFP repositories.
*/

package isabelle


object Sync {
  /* session images */

  def find_images(options: Options, session_images: List[String],
    dirs: List[Path] = Nil
  ): List[String] = {
    if (session_images.isEmpty) Nil
    else {
      val store = Store(options)
      val sessions_structure = Sessions.load_structure(options, dirs = dirs)
      sessions_structure.build_requirements(session_images).flatMap { name =>
        val session = store.get_session(name)
        val heap =
          session.heap.map(_.expand).map(path =>
            File.standard_path(path.dir.dir) + "/./" + path.dir.file_name + "/" + path.file_name)
        val log_db =
          session.log_db.map(_.expand).map(path =>
            File.standard_path(path.dir.dir.dir) + "/./" + path.dir.dir.file_name + "/" +
              path.dir.file_name + "/" + path.file_name)
        heap.toList ::: log_db.toList
      }
    }
  }


  /* sync */

  val DIRS: Path = Path.basic("dirs")
  val DIRS_ROOTS: Path = DIRS + Sessions.ROOTS

  sealed case class Dir(name: String, root: Path, path: Path = Path.current, rev: String = "") {
    lazy val hg: Mercurial.Repository = Mercurial.repository(root)
    def check(): Unit = hg

    def source: Path = root + path
    def target: Path = DIRS + Path.basic(name)
    def roots_entry: String = ((if (name.isEmpty) Path.parent else Path.basic(name)) + path).implode
  }

  def afp_dir(base_dir: Path = AFP.BASE, rev: String = ""): Dir =
    Dir("AFP", base_dir, path = AFP.main_dir(base_dir = Path.current), rev = rev)

  def afp_dirs(root: Option[Path] = None, rev: String = ""): List[Dir] =
    root.toList.map(base_dir => afp_dir(base_dir = base_dir, rev = rev))

  def sync(options: Options, context: Rsync.Context, target: Path,
    thorough: Boolean = false,
    purge_heaps: Boolean = false,
    session_images: List[String] = Nil,
    preserve_jars: Boolean = false,
    dry_run: Boolean = false,
    rev: String = "",
    dirs: List[Dir] = Nil
  ): Unit = {
    val progress = context.progress

    val self = Mercurial.self_repository()
    dirs.foreach(_.check())

    val sync_dirs: List[Dir] = {
      val m =
        Multi_Map.from(
          for (dir <- dirs.iterator if dir.name.nonEmpty) yield dir.name -> dir.root.canonical)
      for ((name, roots) <- m.iterator_list if roots.length > 1) {
        error("Incoherent sync directory " + quote(name) + ":\n" +
          cat_lines(roots.reverse.map(p => "  " + p.toString)))
      }
      Library.distinct(dirs, (d1: Dir, d2: Dir) => d1.name == d2.name)
    }

    val more_filter = if (preserve_jars) List("include *.jar", "protect *.jar") else Nil

    def synchronize(src: Mercurial.Repository, dest: Path, r: String,
      contents: List[File.Content] = Nil, filter: List[String] = Nil
    ): Unit = {
      src.sync(context, dest, rev = r, thorough = thorough, dry_run = dry_run,
        contents = contents, filter = filter ::: more_filter)
    }

    progress.echo("\n* Isabelle:", verbose = true)
    val filter_heaps = if (purge_heaps) Nil else List("protect /heaps", "protect /heaps/**")
    val filter_dirs = sync_dirs.map(dir => "protect /" + dir.target.implode)
    synchronize(self, target, rev,
      contents = List(File.content(Path.explode("etc/ISABELLE_ID"), self.id(rev = rev))),
      filter = filter_heaps ::: filter_dirs)

    context.ssh.make_directory(target + DIRS)
    context.ssh.write(target + DIRS_ROOTS, Library.terminate_lines(dirs.map(_.roots_entry)))

    for (dir <- sync_dirs) {
      progress.echo("\n* " + dir.name + ":", verbose = true)
      synchronize(dir.hg, target + dir.target, dir.rev)
    }

    val images = find_images(options, session_images, dirs = dirs.map(_.source))
    if (images.nonEmpty) {
      progress.echo("\n* Session images:", verbose = true)
      val heaps = context.target(target + Path.explode("heaps")) + "/"
      Rsync.exec(context, thorough = thorough, dry_run = dry_run,
        args = List("--relative", "--") ::: images ::: List(heaps)).check
    }
  }

  val isabelle_tool =
    Isabelle_Tool("sync", "synchronize Isabelle + AFP repositories",
      Scala_Project.here, { args =>
        var afp_root: Option[Path] = None
        var purge_heaps = false
        var session_images = List.empty[String]
        var preserve_jars = false
        var thorough = false
        var afp_rev = ""
        var dry_run = false
        var ssh_port = 0
        var rev = ""
        var ssh_host = ""
        var ssh_user = ""
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle sync [OPTIONS] TARGET

  Options are:
    -A ROOT      include AFP with given root directory (":" for """ + AFP.BASE.implode + """)
    -H           purge heaps directory on target
    -I NAME      include session heap image and build database
                 (based on accidental local state)
    -J           preserve *.jar files
    -T           thorough treatment of file content and directory times
    -a REV       explicit AFP revision (default: state of working directory)
    -s HOST      SSH host name for remote target (default: local)
    -u USER      explicit SSH user name
    -n           no changes: dry-run
    -p PORT      explicit SSH port
    -r REV       explicit revision (default: state of working directory)
    -v           verbose

  Synchronize Isabelle + AFP repositories, based on "isabelle hg_sync".
""",
          "A:" -> (arg => afp_root = Some(if (arg == ":") AFP.BASE else Path.explode(arg))),
          "H" -> (_ => purge_heaps = true),
          "I:" -> (arg => session_images = session_images ::: List(arg)),
          "J" -> (_ => preserve_jars = true),
          "T" -> (_ => thorough = true),
          "a:" -> (arg => afp_rev = arg),
          "n" -> (_ => dry_run = true),
          "p:" -> (arg => ssh_port = Value.Int.parse(arg)),
          "r:" -> (arg => rev = arg),
          "s:" -> (arg => ssh_host = arg),
          "u:" -> (arg => ssh_user = arg),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        val target =
          more_args match {
            case List(target) => Path.explode(target)
            case _ => getopts.usage()
          }

        val options = Options.init()
        val progress = new Console_Progress(verbose = verbose)

        using(SSH.open_system(options, host = ssh_host, port = ssh_port, user = ssh_user)) { ssh =>
          val context = Rsync.Context(progress = progress, ssh = ssh, stats = verbose)
          sync(options, context, target, thorough = thorough, purge_heaps = purge_heaps,
            session_images = session_images, preserve_jars = preserve_jars, dry_run = dry_run,
            rev = rev, dirs = afp_dirs(afp_root, afp_rev))
        }
      }
    )
}
