/*  Title:      Pure/General/mercurial.scala
    Author:     Makarius

Support for Mercurial repositories, with local or remote repository clone
and working directory (via ssh connection).
*/

package isabelle


import scala.annotation.tailrec
import scala.collection.mutable


object Mercurial
{
  type Graph = isabelle.Graph[String, Unit]


  /* HTTP server */

  object Server
  {
    def apply(root: String): Server = new Server(root)

    def start(root: Path): Server =
    {
      val hg = repository(root)

      val server_process = Future.promise[Bash.Process]
      val server_root = Future.promise[String]
      Isabelle_Thread.fork("hg") {
        val process =
          Exn.capture { Bash.process(hg.command_line("serve", options = "--port 0 --print-url")) }
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

  class Server private(val root: String) extends AutoCloseable
  {
    override def toString: String = root

    def close(): Unit = ()

    def changeset(rev: String = "tip", raw: Boolean = false): String =
      root + (if (raw) "/raw-rev/" else "/rev/") + rev

    def file(path: Path, rev: String = "tip", raw: Boolean = false): String =
      root + (if (raw) "/raw-file/" else "/file/") + rev + "/" + path.expand.implode

    def archive(rev: String = "tip"): String =
      root + "/archive/" + rev + ".tar.gz"

    def read_changeset(rev: String = "tip"): String =
      Url.read(changeset(rev = rev, raw = true))

    def read_file(path: Path, rev: String = "tip"): String =
      Url.read(file(path, rev = rev, raw = true))

    def download_archive(rev: String = "tip", progress: Progress = new Progress): HTTP.Content =
      Isabelle_System.download(archive(rev = rev), progress = progress)

    def download_dir(dir: Path, rev: String = "tip", progress: Progress = new Progress): Unit =
    {
      Isabelle_System.new_directory(dir)
      Isabelle_System.with_tmp_file("rev", ext = ".tar.gz")(archive_path =>
      {
        val content = download_archive(rev = rev, progress = progress)
        Bytes.write(archive_path, content.bytes)
        progress.echo("Unpacking " + rev + ".tar.gz")
        Isabelle_System.gnutar("-xzf " + File.bash_path(archive_path) + " --strip-components=1",
          dir = dir, original_owner = true).check
      })
    }
  }


  /* command-line syntax */

  def optional(s: String, prefix: String = ""): String =
    if (s == "") "" else " " + prefix + " " + Bash.string(s)

  def opt_flag(flag: String, b: Boolean): String = if (b) " " + flag else ""
  def opt_rev(s: String): String = optional(s, "--rev")
  def opt_template(s: String): String = optional(s, "--template")


  /* repository archives */

  private val Archive_Node = """^node: (\S{12}).*$""".r
  private val Archive_Tag = """^tag: (\S+).*$""".r

  sealed case class Archive_Info(lines: List[String])
  {
    def id: Option[String] = lines.collectFirst({ case Archive_Node(a) => a })
    def tags: List[String] = for (Archive_Tag(tag) <- lines if tag != "tip") yield tag
  }

  def archive_info(root: Path): Option[Archive_Info] =
  {
    val path = root + Path.explode(".hg_archival.txt")
    if (path.is_file) Some(Archive_Info(Library.trim_split_lines(File.read(path)))) else None
  }

  def archive_id(root: Path): Option[String] =
    archive_info(root).flatMap(_.id)

  def archive_tags(root: Path): Option[String] =
    archive_info(root).map(info => info.tags.mkString(" "))


  /* repository access */

  def is_repository(root: Path, ssh: SSH.System = SSH.Local): Boolean =
    ssh.is_dir(root + Path.explode(".hg")) &&
    new Repository(root, ssh).command("root").ok

  def repository(root: Path, ssh: SSH.System = SSH.Local): Repository =
  {
    val hg = new Repository(root, ssh)
    hg.command("root").check
    hg
  }

  def find_repository(start: Path, ssh: SSH.System = SSH.Local): Option[Repository] =
  {
    @tailrec def find(root: Path): Option[Repository] =
      if (is_repository(root, ssh)) Some(repository(root, ssh = ssh))
      else if (root.is_root) None
      else find(root + Path.parent)

    find(ssh.expand_path(start))
  }

  private def make_repository(root: Path, cmd: String, args: String, ssh: SSH.System = SSH.Local)
    : Repository =
  {
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

  def setup_repository(source: String, root: Path, ssh: SSH.System = SSH.Local): Repository =
  {
    if (ssh.is_dir(root)) { val hg = repository(root, ssh = ssh); hg.pull(remote = source); hg }
    else clone_repository(source, root, options = "--noupdate", ssh = ssh)
  }

  class Repository private[Mercurial](root_path: Path, ssh: SSH.System = SSH.Local)
  {
    hg =>

    val root: Path = ssh.expand_path(root_path)
    def root_url: String = ssh.hg_url + root.implode

    override def toString: String = ssh.hg_url + root.implode

    def command_line(name: String, args: String = "", options: String = "",
      repository: Boolean = true): String =
    {
      "export LANG=C HGPLAIN=\n\"${HG:-hg}\" --config " + Bash.string("defaults." + name + "=") +
        (if (repository) " --repository " + ssh.bash_path(root) else "") +
        " --noninteractive " + name + " " + options + " " + args
    }

    def command(
      name: String, args: String = "", options: String = "",
      repository: Boolean = true):  Process_Result =
    {
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

    def tags(rev: String = "tip"): String =
    {
      val result = identify(rev, options = "-t")
      Library.space_explode(' ', result).filterNot(_ == "tip").mkString(" ")
    }

    def paths(args: String = "", options: String = ""): List[String] =
      hg.command("paths", args = args, options = options).check.out_lines

    def manifest(rev: String = "", options: String = ""): List[String] =
      hg.command("manifest", opt_rev(rev), options).check.out_lines

    def log(rev: String = "", template: String = "", options: String = ""): String =
      hg.command("log", opt_rev(rev) + opt_template(template), options).check.out

    def parent(): String = log(rev = "p1()", template = "{node|short}")

    def push(
      remote: String = "", rev: String = "", force: Boolean = false, options: String = ""): Unit =
    {
      hg.command("push", opt_rev(rev) + opt_flag("--force", force) + optional(remote), options).
        check_rc(rc => rc == 0 | rc == 1)
    }

    def pull(remote: String = "", rev: String = "", options: String = ""): Unit =
      hg.command("pull", opt_rev(rev) + optional(remote), options).check

    def update(
      rev: String = "", clean: Boolean = false, check: Boolean = false, options: String = ""): Unit =
    {
      hg.command("update",
        opt_rev(rev) + opt_flag("--clean", clean) + opt_flag("--check", check), options).check
    }

    def known_files(): List[String] =
      hg.command("status", options = "--modified --added --clean --no-status").check.out_lines

    def graph(): Graph =
    {
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
  }


  /* check files */

  def check_files(files: List[Path], ssh: SSH.System = SSH.Local): (List[Path], List[Path]) =
  {
    val outside = new mutable.ListBuffer[Path]
    val unknown = new mutable.ListBuffer[Path]

    @tailrec def check(paths: List[Path]): Unit =
    {
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


  /* setup remote vs. local repository */

  private def edit_hgrc(local_hg: Repository, path_name: String, source: String): Unit =
  {
    val hgrc = local_hg.root + Path.explode(".hg/hgrc")
    def header(line: String): Boolean = line.startsWith("[paths]")
    val Entry = """^(\S+)\s*=\s*(.*)$""".r
    val new_entry = path_name + " = " + source

    def commit(lines: List[String]): Boolean =
    {
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
    progress: Progress = new Progress): Unit =
  {
    /* local repository */

    Isabelle_System.make_directory(local_path)

    val repos_name =
      proper_string(remote_name) getOrElse local_path.absolute.base.implode

    val local_hg =
      if (is_repository(local_path)) repository(local_path)
      else init_repository(local_path)

    progress.echo("Local repository " + local_hg.root.absolute)


    /* remote repository */

    val remote_url =
      remote match {
        case _ if remote.startsWith("ssh://") =>
          val ssh_url = remote + "/" + repos_name

          if (!remote_exists) {
            try { local_hg.command("init", ssh_url, repository = false).check }
            catch { case ERROR(msg) => progress.echo_warning(msg) }
          }

          ssh_url

        case SSH.Target(user, host) =>
          val phabricator = Phabricator.API(user, host)

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
            Time.seconds(0.5).sleep
            repos = phabricator.the_repository(repos.phid)
          }

          repos.ssh_url

        case _ => error("Malformed remote specification " + quote(remote))
      }

    progress.echo("Remote repository " + quote(remote_url))


    /* synchronize local and remote state */

    progress.echo("Synchronizing ...")

    edit_hgrc(local_hg, path_name, remote_url)

    local_hg.pull(options = "-u")

    local_hg.push(remote = remote_url)
  }

  val isabelle_tool =
    Isabelle_Tool("hg_setup", "setup remote vs. local Mercurial repository",
      Scala_Project.here, args =>
    {
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
}
