/*  Title:      Pure/General/mercurial.scala
    Author:     Makarius

Support for Mercurial repositories, with local or remote repository clone
and working directory (via ssh connection).
*/

package isabelle


import scala.annotation.tailrec
import scala.collection.mutable


object Mercurial {
  type Graph = isabelle.Graph[String, Unit]



  /** HTTP server **/

  object Server {
    def apply(root: String): Server = new Server(root)

    def start(root: Path): Server = {
      val hg = repository(root)

      val server_process = Future.promise[Bash.Process]
      val server_root = Future.promise[String]
      Isabelle_Thread.fork("hg") {
        val process =
          Exn.result { Bash.process(hg.command_line("serve", options = "--port 0 --print-url")) }
        server_process.fulfill_result(process)
        Exn.release(process).result(progress_stdout =
          line => if (!server_root.is_finished) {
            server_root.fulfill(Library.try_unsuffix("/", line).getOrElse(line))
          })
      }
      server_process.join

      new Server(server_root.join) {
        override def close(): Unit = server_process.join.terminate()
      }
    }
  }

  class Server private(val root: String) extends AutoCloseable {
    override def toString: String = root

    def close(): Unit = ()

    def changeset(rev: String = "tip", raw: Boolean = false): String =
      root + (if (raw) "/raw-rev/" else "/rev/") + rev

    def file(path: Path, rev: String = "tip", raw: Boolean = false): String =
      root + (if (raw) "/raw-file/" else "/file/") + rev + "/" + File.standard_path(path)

    def archive(rev: String = "tip"): String =
      root + "/archive/" + rev + ".tar.gz"

    def read_changeset(rev: String = "tip"): String =
      Url.read(changeset(rev = rev, raw = true))

    def read_file(path: Path, rev: String = "tip"): String =
      Url.read(file(path, rev = rev, raw = true))

    def download_archive(rev: String = "tip", progress: Progress = new Progress): HTTP.Content =
      Isabelle_System.download(archive(rev = rev), progress = progress)

    def download_dir(dir: Path, rev: String = "tip", progress: Progress = new Progress): Unit = {
      Isabelle_System.new_directory(dir)
      Isabelle_System.with_tmp_file("rev", ext = ".tar.gz") { archive_path =>
        val content = download_archive(rev = rev, progress = progress)
        Bytes.write(archive_path, content.bytes)
        progress.echo("Unpacking " + rev + ".tar.gz")
        Isabelle_System.gnutar("-xzf " + File.bash_path(archive_path),
          dir = dir, original_owner = true, strip = true).check
      }
    }
  }



  /** repository commands **/

  /* command-line syntax */

  def optional(s: String, prefix: String = ""): String =
    if_proper(s, " " + prefix + " " + Bash.string(s))

  def opt_flag(flag: String, b: Boolean): String = if (b) " " + flag else ""
  def opt_rev(s: String): String = optional(s, "--rev")
  def opt_template(s: String): String = optional(s, "--template")


  /* repository archives */

  private val Archive_Node = """^node: (\S{12}).*$""".r
  private val Archive_Tag = """^tag: (\S+).*$""".r

  sealed case class Archive_Info(lines: List[String]) {
    def id: Option[String] = lines.collectFirst({ case Archive_Node(a) => a })
    def tags: List[String] = for (case Archive_Tag(tag) <- lines if tag != "tip") yield tag
  }

  def archive_info(root: Path): Option[Archive_Info] = {
    val path = root + Path.explode(".hg_archival.txt")
    if (path.is_file) Some(Archive_Info(Library.trim_split_lines(File.read(path)))) else None
  }

  def archive_id(root: Path): Option[String] =
    archive_info(root).flatMap(_.id)

  def archive_tags(root: Path): Option[String] =
    archive_info(root).map(info => info.tags.mkString(" "))


  /* hg_sync meta data */

  def sync_id(root: Path, ssh: SSH.System = SSH.Local): Option[String] =
    if (Hg_Sync.ok(root, ssh)) Some(Hg_Sync.directory(root, ssh).id) else None

  object Hg_Sync {
    val NAME = ".hg_sync"
    val _NAME: String = " " + NAME
    val PATH: Path = Path.explode(NAME)
    val PATH_ID: Path = PATH + Path.explode("id")
    val PATH_LOG: Path = PATH + Path.explode("log")
    val PATH_DIFF: Path = PATH + Path.explode("diff")
    val PATH_STAT: Path = PATH + Path.explode("stat")

    def ok(root: Path, ssh: SSH.System = SSH.Local): Boolean = ssh.is_dir(root + PATH)

    def check_directory(root: Path, ssh: SSH.System = SSH.Local): Unit =
      if (ssh.is_dir(root) && !ok(root, ssh = ssh) && ssh.read_dir(root).nonEmpty) {
        error("No .hg_sync meta data in " + ssh.rsync_path(root))
      }

    def directory(root: Path, ssh: SSH.System = SSH.Local): Directory = {
      if (ok(root, ssh = ssh)) new Directory(root, ssh)
      else error("No .hg_sync directory found in " + ssh.rsync_path(root))
    }

    class Directory private [Hg_Sync](val root: Path, val ssh: SSH.System)
    {
      override def toString: String = ssh.rsync_path(root)

      def read(path: Path): String = ssh.read(root + path)
      lazy val id: String = read(PATH_ID)
      lazy val log: String = read(PATH_LOG)
      lazy val diff: String = read(PATH_DIFF)
      lazy val stat: String = read(PATH_STAT)

      def changed: Boolean = id.endsWith("+")
    }
  }


  /* repository access */

  def detect_repository(root: Path, ssh: SSH.System = SSH.Local): Option[Repository] =
    if (ssh.is_dir(root + Path.explode(".hg"))) {
      val hg = new Repository(root, ssh)
      val result = hg.command("root")
      if (result.ok && ssh.eq_file(root, Path.explode(result.out))) Some(hg) else None
    }
    else None

  def is_repository(root: Path, ssh: SSH.System = SSH.Local): Boolean =
    detect_repository(root, ssh = ssh).isDefined

  def id_repository(root: Path, ssh: SSH.System = SSH.Local, rev: String = "tip"): Option[String] =
    for (hg <- detect_repository(root, ssh = ssh)) yield hg.id(rev = rev)

  def repository(root: Path, ssh: SSH.System = SSH.Local): Repository =
    detect_repository(root, ssh = ssh) getOrElse error("Bad hg repository " + ssh.expand_path(root))

  def self_repository(): Repository = repository(Path.ISABELLE_HOME)

  def find_repository(start: Path, ssh: SSH.System = SSH.Local): Option[Repository] =
    ssh.find_path(start, detect_repository(_, ssh = ssh))

  def the_repository(start: Path, ssh: SSH.System = SSH.Local): Repository =
    find_repository(start, ssh = ssh) getOrElse
      error("No repository found in " + start.absolute)

  private def make_repository(
    root: Path,
    cmd: String,
    args: String,
    ssh: SSH.System = SSH.Local
  ) : Repository = {
    val hg = new Repository(root, ssh)
    ssh.make_directory(hg.root.dir)
    hg.command(cmd, args, repository = false).check
    hg
  }

  def init_repository(root: Path, ssh: SSH.System = SSH.Local): Repository =
    make_repository(root, "init", ssh.bash_path(root), ssh = ssh)

  def clone_repository(source: String, root: Path,
      rev: String = "", options: String = "", ssh: SSH.System = SSH.Local): Repository =
    make_repository(root, "clone",
      options + " " + Bash.string(source) + " " + ssh.bash_path(root) + opt_rev(rev), ssh = ssh)

  def setup_repository(source: String, root: Path, ssh: SSH.System = SSH.Local): Repository = {
    if (ssh.is_dir(root)) { val hg = repository(root, ssh = ssh); hg.pull(remote = source); hg }
    else clone_repository(source, root, options = "--noupdate", ssh = ssh)
  }

  class Repository private[Mercurial](root_path: Path, ssh: SSH.System = SSH.Local) {
    hg =>

    val root: Path = ssh.expand_path(root_path)
    def root_url: String = ssh.hg_url + root.implode

    override def toString: String = ssh.hg_url + root.implode

    def command_line(
      name: String,
      args: String = "",
      options: String = "",
      repository: Boolean = true
    ): String = {
      "export LANG=C HGPLAIN=\n\"${HG:-hg}\" --config " + Bash.string("defaults." + name + "=") +
        (if (repository) " --repository " + ssh.bash_path(root) else "") +
        " --noninteractive " + name + " " + options + " " + args
    }

    def command(
      name: String,
      args: String = "",
      options: String = "",
      repository: Boolean = true
    ): Process_Result = {
      ssh.execute(command_line(name, args = args, options = options, repository = repository))
    }

    def add(files: List[Path]): Unit =
      hg.command("add", files.map(ssh.bash_path).mkString(" "))

    def archive(target: String, rev: String = "", options: String = ""): Unit =
      hg.command("archive", opt_rev(rev) + " " + Bash.string(target), options).check

    def heads(template: String = "{node|short}\n", options: String = ""): List[String] =
      hg.command("heads", opt_template(template), options).check.out_lines

    def identify(rev: String = "tip", options: String = ""): String =
      hg.command("id", opt_rev(rev), options).check.out_lines.headOption getOrElse ""

    def id(rev: String = "tip"): String = identify(rev, options = "-i")

    def tags(rev: String = "tip"): String = {
      val result = identify(rev, options = "-t")
      space_explode(' ', result).filterNot(_ == "tip").mkString(" ")
    }

    def paths(args: String = "", options: String = ""): List[String] =
      hg.command("paths", args = args, options = options).check.out_lines

    def manifest(rev: String = "", options: String = ""): List[String] =
      hg.command("manifest", opt_rev(rev), options).check.out_lines

    def log(rev: String = "", template: String = "", options: String = ""): String =
      hg.command("log", opt_rev(rev) + opt_template(template), options).check.out

    def diff(rev: String = "", options: String = ""): String =
      hg.command("diff", opt_rev(rev), options).check.out

    def parent(): String = log(rev = "p1()", template = "{node|short}")

    def push(
      remote: String = "",
      rev: String = "",
      force: Boolean = false,
      options: String = ""
    ): Unit = {
      hg.command("push", opt_rev(rev) + opt_flag("--force", force) + optional(remote), options).
        check_rc(rc => rc == 0 | rc == 1)
    }

    def pull(remote: String = "", rev: String = "", options: String = ""): Unit =
      hg.command("pull", opt_rev(rev) + optional(remote), options).check

    def update(
      rev: String = "",
      clean: Boolean = false,
      check: Boolean = false,
      options: String = ""
    ): Unit = {
      hg.command("update",
        opt_rev(rev) + opt_flag("--clean", clean) + opt_flag("--check", check), options).check
    }

    def status(options: String = ""): List[String] =
      hg.command("status", options = options).check.out_lines

    def known_files(): List[String] = status(options = "--modified --added --clean --no-status")

    def sync(context: Rsync.Context, target: Path,
      thorough: Boolean = false,
      dry_run: Boolean = false,
      filter: List[String] = Nil,
      contents: List[File.Content] = Nil,
      rev: String = ""
    ): Unit = {
      require(ssh.is_local, "local repository required")

      Isabelle_System.with_tmp_dir("sync") { tmp_dir =>
        Hg_Sync.check_directory(target, ssh = context.ssh)

        val id_content = id(rev = rev)
        val is_changed = id_content.endsWith("+")
        val log_content = if (is_changed) "" else log(rev = rev, options = "-l1")
        val diff_content = if (is_changed) diff(rev = rev, options = "--git") else ""
        val stat_content = if (is_changed) diff(rev = rev, options = "--stat") else ""

        val all_contents =
          File.content(Hg_Sync.PATH_ID, id_content) ::
          File.content(Hg_Sync.PATH_LOG, log_content) ::
          File.content(Hg_Sync.PATH_DIFF, diff_content) ::
          File.content(Hg_Sync.PATH_STAT, stat_content) :: contents

        all_contents.foreach(_.write(target, ssh = context.ssh))

        val (exclude, source) =
          if (rev.isEmpty) {
            val exclude = ".hg" :: status(options = "--unknown --ignored --no-status")
            val source = File.standard_path(root)
            (exclude, source)
          }
          else {
            val exclude = List(".hg_archival.txt")
            val source = File.standard_path(tmp_dir + Path.explode("archive"))
            archive(source, rev = rev)
            (exclude, source)
          }

        val exclude_path = tmp_dir + Path.explode("exclude")
        File.write(exclude_path, cat_lines(exclude.map("/" + _)))

        val protect =
          (Hg_Sync.PATH :: contents.map(_.path))
            .map(path => "protect /" + File.standard_path(path))
        Rsync.exec(context,
          thorough = thorough,
          dry_run = dry_run,
          clean = true,
          prune_empty_dirs = true,
          filter = protect ::: filter,
          args = List("--exclude-from=" + exclude_path.implode, "--",
            Url.direct_path(source), context.target(target))
        ).check
      }
    }

    private val cache_graph = Synchronized[(List[String], Graph)]((Nil, Graph.string[Unit]))

    def graph(): Graph =
      cache_graph.change_result({ case (old_topo, old_graph) =>
        val topo = heads(options = "--topo")
        val graph =
          if (topo == old_topo) old_graph
          else {
            val Node = """^node: (\w{12}) (\w{12}) (\w{12})""".r
            val log_result =
              log(template = """node: {node|short} {p1node|short} {p2node|short}\n""")
            split_lines(log_result).foldLeft(Graph.string[Unit]) {
              case (graph, Node(x, y, z)) =>
                val deps = List(y, z).filterNot(s => s.forall(_ == '0'))
                val graph1 = (x :: deps).foldLeft(graph)(_.default_node(_, ()))
                deps.foldLeft(graph1)({ case (g, dep) => g.add_edge(dep, x) })
              case (graph, _) => graph
            }
          }
        (graph, (topo, graph))
      })
  }



  /** check files **/

  def check_files(files: List[Path], ssh: SSH.System = SSH.Local): (List[Path], List[Path]) = {
    val outside = new mutable.ListBuffer[Path]
    val unknown = new mutable.ListBuffer[Path]

    @tailrec def check(paths: List[Path]): Unit = {
      paths match {
        case path :: rest =>
          find_repository(path, ssh) match {
            case None => outside += path; check(rest)
            case Some(hg) =>
              val known =
                hg.known_files().iterator.map(name =>
                  (hg.root + Path.explode(name)).canonical_file).toSet
              if (!known(path.canonical_file)) unknown += path
              check(rest.filterNot(p => known(p.canonical_file)))
          }
        case Nil =>
      }
    }

    check(files)
    (outside.toList, unknown.toList)
  }



  /** hg_setup **/

  private def edit_hgrc(local_hg: Repository, path_name: String, source: String): Unit = {
    val hgrc = local_hg.root + Path.explode(".hg/hgrc")
    def header(line: String): Boolean = line.startsWith("[paths]")
    val Entry = """^(\S+)\s*=\s*(.*)$""".r
    val new_entry = path_name + " = " + source

    def commit(lines: List[String]): Boolean = {
      File.write(hgrc, cat_lines(lines))
      true
    }
    val edited =
      hgrc.is_file && {
        val lines = split_lines(File.read(hgrc))
        lines.count(header) == 1 && {
          if (local_hg.paths(options = "-q").contains(path_name)) {
            val old_source = local_hg.paths(args = path_name).head
            val old_entry = path_name + ".old = " + old_source
            val lines1 =
              lines.map {
                case Entry(a, b) if a == path_name && b == old_source =>
                  new_entry + "\n" + old_entry
                case line => line
              }
            lines != lines1 && commit(lines1)
          }
          else {
            val prefix = lines.takeWhile(line => !header(line))
            val n = prefix.length
            commit(prefix ::: List(lines(n), new_entry) ::: lines.drop(n + 1))
          }
        }
      }
    if (!edited) File.append(hgrc, "\n[paths]\n" + new_entry + "\n")
  }

  val default_path_name = "default"

  def hg_setup(
    remote: String,
    local_path: Path,
    remote_name: String = "",
    path_name: String = default_path_name,
    remote_exists: Boolean = false,
    progress: Progress = new Progress
  ): Unit = {
    /* local repository */

    Isabelle_System.make_directory(local_path)

    val repos_name =
      proper_string(remote_name) getOrElse local_path.absolute.base.implode

    val local_hg = detect_repository(local_path) getOrElse init_repository(local_path)

    progress.echo("Local repository " + local_hg.root.absolute)


    /* remote repository */

    val remote_url = {
      if (remote.startsWith("ssh://")) {
        val ssh_url = remote + "/" + repos_name

        if (!remote_exists) {
          try { local_hg.command("init", ssh_url, repository = false).check }
          catch { case ERROR(msg) => progress.echo_warning(msg) }
        }

        ssh_url
      }
      else {
        val phabricator = Phabricator.API(remote)

        var repos =
          phabricator.get_repositories().find(r => r.short_name == repos_name) getOrElse {
            if (remote_exists) {
              error("Remote repository " +
                quote(phabricator.hg_url + "/source/" + repos_name) + " expected to exist")
            }
            else phabricator.create_repository(repos_name, short_name = repos_name)
          }

        while (repos.importing) {
          progress.echo("Awaiting remote repository ...")
          Time.seconds(0.5).sleep()
          repos = phabricator.the_repository(repos.phid)
        }

        repos.ssh_url
      }
    }

    progress.echo("Remote repository " + quote(remote_url))


    /* synchronize local and remote state */

    progress.echo("Synchronizing ...")

    edit_hgrc(local_hg, path_name, remote_url)

    local_hg.pull(options = "-u")

    local_hg.push(remote = remote_url)
  }

  val isabelle_tool1 =
    Isabelle_Tool("hg_setup", "setup remote vs. local Mercurial repository",
      Scala_Project.here,
      { args =>
        var remote_name = ""
        var path_name = default_path_name
        var remote_exists = false

        val getopts = Getopts("""
Usage: isabelle hg_setup [OPTIONS] REMOTE LOCAL_DIR

  Options are:
    -n NAME      remote repository name (default: base name of LOCAL_DIR)
    -p PATH      Mercurial path name (default: """ + quote(default_path_name) + """)
    -r           assume that remote repository already exists

  Setup a remote vs. local Mercurial repository: REMOTE either refers to a
  Phabricator server "user@host" or SSH file server "ssh://user@host/path".
""",
          "n:" -> (arg => remote_name = arg),
          "p:" -> (arg => path_name = arg),
          "r" -> (_ => remote_exists = true))

        val more_args = getopts(args)

        val (remote, local_path) =
          more_args match {
            case List(arg1, arg2) => (arg1, Path.explode(arg2))
            case _ => getopts.usage()
          }

        val progress = new Console_Progress

        hg_setup(remote, local_path, remote_name = remote_name, path_name = path_name,
          remote_exists = remote_exists, progress = progress)
      })



  /** hg_sync **/

  val isabelle_tool2 =
    Isabelle_Tool("hg_sync", "synchronize Mercurial repository with target directory",
      Scala_Project.here, { args =>
        var filter: List[String] = Nil
        var root: Option[Path] = None
        var thorough = false
        var dry_run = false
        var options = Options.init()
        var ssh_port = 0
        var rev = ""
        var ssh_host = ""
        var ssh_user = ""
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle hg_sync [OPTIONS] TARGET

  Options are:
    -F RULE      add rsync filter RULE
                 (e.g. "protect /foo" to avoid deletion)
    -R ROOT      explicit repository root directory
                 (default: implicit from current directory)
    -T           thorough treatment of file content and directory times
    -n           no changes: dry-run
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -p PORT      explicit SSH port
    -r REV       explicit revision (default: state of working directory)
    -s HOST      SSH host name for remote target (default: local)
    -u USER      explicit SSH user name
    -v           verbose

  Synchronize Mercurial repository with TARGET directory,
  which can be local or remote (see options -s -p -u).
""",
          "F:" -> (arg => filter = filter ::: List(arg)),
          "R:" -> (arg => root = Some(Path.explode(arg))),
          "T" -> (_ => thorough = true),
          "n" -> (_ => dry_run = true),
          "o:" -> (arg => options = options + arg),
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

        val progress = new Console_Progress(verbose = verbose)
        val hg =
          root match {
            case Some(dir) => repository(dir)
            case None => the_repository(Path.current)
          }

        using(SSH.open_system(options, host = ssh_host, port = ssh_port, user = ssh_user)) { ssh =>
          val context = Rsync.Context(progress = progress, ssh = ssh, stats = verbose)
          hg.sync(context, target, thorough = thorough, dry_run = dry_run,
            filter = filter, rev = rev)
        }
      }
    )
}
