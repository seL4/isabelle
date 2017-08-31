/*  Title:      Pure/General/mercurial.scala
    Author:     Makarius

Support for Mercurial repositories, with local or remote repository clone
and working directory (via ssh connection).
*/

package isabelle


import java.io.{File => JFile}

import scala.annotation.tailrec
import scala.collection.mutable


object Mercurial
{
  /* command-line syntax */

  def optional(s: String, prefix: String = ""): String =
    if (s == "") "" else " " + prefix + " " + Bash.string(s)

  def opt_flag(flag: String, b: Boolean): String = if (b) " " + flag else ""
  def opt_rev(s: String): String = optional(s, "--rev")
  def opt_template(s: String): String = optional(s, "--template")


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
    def find(root: Path): Option[Repository] =
      if (is_repository(root, ssh)) Some(repository(root, ssh = ssh))
      else if (root.is_root) None
      else find(root + Path.parent)

    find(ssh.expand_path(start))
  }

  def clone_repository(source: String, root: Path, rev: String = "", options: String = "",
    ssh: SSH.System = SSH.Local): Repository =
  {
    val hg = new Repository(root, ssh)
    ssh.mkdirs(hg.root.dir)
    hg.command("clone", Bash.string(source) + " " + File.bash_path(hg.root) + opt_rev(rev), options)
      .check
    hg
  }

  def setup_repository(source: String, root: Path, ssh: SSH.System = SSH.Local): Repository =
  {
    if (ssh.is_dir(root)) { val hg = repository(root, ssh = ssh); hg.pull(remote = source); hg }
    else clone_repository(source, root, options = "--noupdate", ssh = ssh)
  }

  class Repository private[Mercurial](root_path: Path, ssh: SSH.System = SSH.Local)
  {
    hg =>

    val root = ssh.expand_path(root_path)
    def root_url: String = ssh.hg_url + root.implode

    override def toString: String = ssh.prefix + root.implode

    def command(name: String, args: String = "", options: String = ""): Process_Result =
    {
      val cmdline =
        "\"${HG:-hg}\" --config " + Bash.string("defaults." + name + "=") +
          (if (name == "clone") "" else " --repository " + File.bash_path(root)) +
          " --noninteractive " + name + " " + options + " " + args
      ssh.execute(cmdline)
    }

    def archive(target: String, rev: String = "", options: String = ""): Unit =
      hg.command("archive", opt_rev(rev) + " " + Bash.string(target), options).check

    def heads(template: String = "{node|short}\n", options: String = ""): List[String] =
      hg.command("heads", opt_template(template), options).check.out_lines

    def identify(rev: String = "tip", options: String = ""): String =
      hg.command("id", opt_rev(rev), options).check.out_lines.headOption getOrElse ""

    def id(rev: String = "tip"): String = identify(rev, options = "-i")

    def manifest(rev: String = "", options: String = ""): List[String] =
      hg.command("manifest", opt_rev(rev), options).check.out_lines

    def log(rev: String = "", template: String = "", options: String = ""): String =
      hg.command("log", opt_rev(rev) + opt_template(template), options).check.out

    def push(remote: String = "", rev: String = "", force: Boolean = false, options: String = "")
    {
      hg.command("push", opt_rev(rev) + opt_flag("--force", force) + optional(remote), options).
        check_rc(rc => rc == 0 | rc == 1)
    }

    def pull(remote: String = "", rev: String = "", options: String = ""): Unit =
      hg.command("pull", opt_rev(rev) + optional(remote), options).check

    def update(
      rev: String = "", clean: Boolean = false, check: Boolean = false, options: String = "")
    {
      hg.command("update",
        opt_rev(rev) + opt_flag("--clean", clean) + opt_flag("--check", check), options).check
    }

    def known_files(): List[String] =
      hg.command("status", options = "--modified --added --clean --no-status").check.out_lines

    def graph(): Graph[String, Unit] =
    {
      val Node = """^node: (\w{12}) (\w{12}) (\w{12})""".r
      val log_result =
        log(template = """node: {node|short} {p1node|short} {p2node|short}\n""")
      (Graph.string[Unit] /: split_lines(log_result)) {
        case (graph, Node(x, y, z)) =>
          val deps = List(y, z).filterNot(s => s.forall(_ == '0'))
          val graph1 = (graph /: (x :: deps))(_.default_node(_, ()))
          (graph1 /: deps)({ case (g, dep) => g.add_edge(dep, x) })
        case (graph, _) => graph
      }
    }
  }


  /* unknown files */

  def unknown_files(files: List[Path], ssh: SSH.System = SSH.Local): List[Path] =
  {
    val unknown = new mutable.ListBuffer[Path]

    @tailrec def check(paths: List[Path])
    {
      paths match {
        case path :: rest =>
          find_repository(path, ssh) match {
            case None => unknown += path; check(rest)
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
    unknown.toList
  }
}
