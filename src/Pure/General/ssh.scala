/*  Title:      Pure/General/ssh.scala
    Author:     Makarius

SSH client on top of OpenSSH command-line tools, preferably with connection
multiplexing, but this does not work on Windows.
*/

package isabelle


import java.util.{Map => JMap}
import java.io.{File => JFile}

import scala.annotation.tailrec


object SSH {
  /* client command */

  def client_command(port: Int = 0, control_path: String = ""): String =
    if (control_path.isEmpty || control_path == Bash.string(control_path)) {
      "ssh" +
        (if (port > 0) " -p " + port else "") +
        if_proper(control_path, " -o ControlPath=" + control_path)
    }
    else error ("Malformed SSH control socket: " + quote(control_path))


  /* OpenSSH configuration and command-line */

  // see https://linux.die.net/man/5/ssh_config
  object Config {
    def entry(x: String, y: String): String = x + "=" + y
    def entry(x: String, y: Int): String = entry(x, y.toString)
    def entry(x: String, y: Long): String = entry(x, y.toString)
    def entry(x: String, y: Boolean): String = entry(x, if (y) "yes" else "no")

    def make(options: Options,
      port: Int = 0,
      user: String = "",
      control_master: Boolean = false,
      control_path: String = ""
    ): List[String] = {
      val ssh_batch_mode = options.bool("ssh_batch_mode")
      val ssh_compression = options.bool("ssh_compression")
      val ssh_alive_interval = options.real("ssh_alive_interval").round
      val ssh_alive_count_max = options.int("ssh_alive_count_max")

      List(
        entry("BatchMode", ssh_batch_mode),
        entry("Compression", ssh_compression)) :::
      (if (ssh_alive_interval >= 0) List(entry("ServerAliveInterval", ssh_alive_interval)) else Nil) :::
      (if (ssh_alive_count_max >= 0) List(entry("ServerAliveCountMax", ssh_alive_count_max)) else Nil) :::
      (if (port > 0) List(entry("Port", port)) else Nil) :::
      (if (user.nonEmpty) List(entry("User", user)) else Nil) :::
      (if (control_master) List("ControlMaster=yes", "ControlPersist=yes") else Nil) :::
      (if (control_path.nonEmpty) List("ControlPath=" + control_path) else Nil)
    }

    def option(entry: String): String = "-o " + Bash.string(entry)
    def option(x: String, y: String): String = option(entry(x, y))
    def option(x: String, y: Int): String = option(entry(x, y))
    def option(x: String, y: Long): String = option(entry(x, y))
    def option(x: String, y: Boolean): String = option(entry(x, y))

    def command(command: String, config: List[String]): String =
      Bash.string(command) + config.map(entry => " " + option(entry)).mkString
  }

  def sftp_string(str: String): String = {
    val special = "[]?*\\{} \"'"
    if (str.isEmpty) "\"\""
    else if (str.exists(special.contains)) {
      val res = new StringBuilder
      for (c <- str) {
        if (special.contains(c)) res += '\\'
        res += c
      }
      res.toString()
    }
    else str
  }


  /* local host (not "localhost") */

  val LOCAL = "local"

  def is_local(host: String): Boolean = host.isEmpty || host == LOCAL

  def print_local(host: String): String = if (is_local(host)) LOCAL else host


  /* open session */

  def open_session(
    options: Options,
    host: String,
    port: Int = 0,
    user: String = "",
    user_home: String = ""
  ): Session = {
    if (is_local(host)) error("Illegal SSH host name " + quote(host))

    val multiplex = options.bool("ssh_multiplexing") && !Platform.is_windows
    val (control_master, control_path) =
      if (multiplex) (true, Isabelle_System.tmp_file("ssh", initialized = false).getPath)
      else (false, "")
    new Session(options, host, port, user, user_home, control_master, control_path)
  }

  class Session private[SSH](
    val options: Options,
    val host: String,
    val port: Int,
    val user: String,
    user_home0: String,
    control_master: Boolean,
    val control_path: String
  ) extends System {
    ssh =>

    override def ssh_session: Option[Session] = Some(ssh)

    def port_suffix: String = if (port > 0) ":" + port else ""
    def user_prefix: String = if_proper(user, user + "@")

    override def toString: String = user_prefix + host + port_suffix
    override def print: String = " (ssh " + toString + ")"
    override def hg_url: String = "ssh://" + toString + "/"
    override def client_command: String =
      SSH.client_command(port = port, control_path = control_path)
    override def rsync_prefix: String = user_prefix + host + ":"


    /* local ssh commands */

    def make_command(
      command: String = "ssh",
      master: Boolean = false,
      opts: String = "",
      args_host: Boolean = false,
      args: String = ""
    ): String = {
      val config =
        Config.make(options, port = port, user = user,
          control_master = master, control_path = control_path)
      val args1 = if_proper(args_host, Bash.string(host) + if_proper(args, " ")) + args
      Config.command(command, config) +
        if_proper(opts, " " + opts) +
        if_proper(args1, " -- " + args1)
    }

    def run_sftp(
      script: String,
      init: Path => Unit = _ => (),
      exit: Path => Unit = _ => ()
    ): Process_Result = {
      Isabelle_System.with_tmp_dir("sftp") { dir =>
        init(dir)
        File.write(dir + Path.explode("script"), script)
        val result =
          Isabelle_System.bash(
            make_command("sftp", opts = "-b script", args_host = true), cwd = dir.file).check
        exit(dir)
        result
      }
    }

    def run_ssh(master: Boolean = false, opts: String = "", args: String = ""): Process_Result =
      Isabelle_System.bash(make_command(master = master, opts = opts, args_host = true, args = args))


    /* init and exit */

    override val home: String = {
      run_ssh(master = control_master, args = "printenv HOME \";\" printenv SHELL").check.out_lines
      match {
        case List(home, shell) =>
          if (shell.endsWith("/bash")) home
          else {
            error("Bad SHELL for " + quote(toString) + " -- expected GNU bash, but found " + shell)
          }
        case _ => error("Malformed remote environment for " + quote(toString))
      }
    }

    override val user_home: String = {
      val path1 =
        try { Path.explode(home).expand_env(Isabelle_System.No_Env) }
        catch { case ERROR(msg) => error(msg + " -- in SSH HOME") }
      val path2 =
        try { Path.explode(user_home0).expand_env(Isabelle_System.No_Env) }
        catch { case ERROR(msg) => error(msg + "-- in SSH USER_HOME") }
      (path1 + path2).implode
    }

    val settings: Isabelle_System.Settings = {
      case "HOME" => home
      case "USER_HOME" => user_home
      case _ => ""
    }

    override def close(): Unit = {
      if (control_path.nonEmpty) run_ssh(opts = "-O exit").check
    }


    /* remote commands */

    override def execute(remote_script: String,
      progress_stdout: String => Unit = (_: String) => (),
      progress_stderr: String => Unit = (_: String) => (),
      redirect: Boolean = false,
      settings: Boolean = true,
      strict: Boolean = true
    ): Process_Result = {
      val remote_script1 = Isabelle_System.export_env(user_home = user_home) + remote_script
      Isabelle_System.bash(make_command(args_host = true, args = Bash.string(remote_script1)),
        progress_stdout = progress_stdout,
        progress_stderr = progress_stderr,
        redirect = redirect,
        strict = strict)
    }

    override def download_file(
      url_name: String,
      file: Path,
      progress: Progress = new Progress
    ): Unit = {
      val cmd_line =
        File.read(Path.explode("~~/lib/scripts/download_file")) + "\n" +
          "download_file " + Bash.string(url_name) + " " + bash_path(file)
      execute(cmd_line,
        progress_stdout = progress.echo(_),
        progress_stderr = progress.echo(_)).check
    }

    override lazy val isabelle_platform: Isabelle_Platform = Isabelle_Platform(ssh = Some(ssh))


    /* remote file-system */

    override def expand_path(path: Path): Path = path.expand_env(settings)
    override def absolute_path(path: Path): Path = {
      val path1 = expand_path(path)
      if (path1.is_absolute) path1 else Path.explode(home) + path1
    }

    def remote_path(path: Path): String = expand_path(path).implode

    override def bash_path(path: Path): String = Bash.string(remote_path(path))
    def sftp_path(path: Path): String = sftp_string(remote_path(path))

    override def is_dir(path: Path): Boolean = run_ssh(args = "test -d " + bash_path(path)).ok
    override def is_file(path: Path): Boolean = run_ssh(args = "test -f " + bash_path(path)).ok

    override def eq_file(path1: Path, path2: Path): Boolean =
      path1 == path2 || execute("test " + bash_path(path1) + " -ef " + bash_path(path2)).ok

    override def delete(path: Path): Unit = {
      val cmd = if (is_dir(path)) "rmdir" else if (is_file(path)) "rm" else ""
      if (cmd.nonEmpty) run_sftp(cmd + " " + sftp_path(path))
    }

    override def restrict(path: Path): Unit =
      if (!execute("chmod g-rwx,o-rwx " + bash_path(path)).ok) {
        error("Failed to change permissions of " + quote(remote_path(path)))
      }

    override def set_executable(path: Path, reset: Boolean = false): Unit =
      if (!execute("chmod a" + (if (reset) "-" else "+") + "x " + bash_path(path)).ok) {
        error("Failed to change executable status of " + quote(remote_path(path)))
      }

    override def make_directory(path: Path): Path = {
      if (!execute("mkdir -p " + bash_path(path)).ok) {
        error("Failed to create directory: " + quote(remote_path(path)))
      }
      path
    }

    override def copy_file(src: Path, dst: Path): Unit = {
      val target = if (is_dir(dst)) dst + expand_path(src).base else dst
      if (!eq_file(src, target)) {
        if (!execute("cp -a " + bash_path(src) + " " + bash_path(target)).ok) {
          error("Failed to copy file " +
            absolute_path(src) + " to " + absolute_path(target) + " (ssh " + toString + ")")
        }
      }
    }

    override def read_dir(path: Path): List[String] =
      run_sftp("@cd " + sftp_path(path) + "\n@ls -1 -a").out_lines.flatMap(s =>
        if (s == "." || s == "..") None
        else Some(Library.perhaps_unprefix("./", s)))

    private def get_file[A](path: Path, f: Path => A): A = {
      var result: Option[A] = None
      run_sftp("get -p " + sftp_path(path) + " local",
        exit = dir => result = Some(f(dir + Path.explode("local"))))
      result.get
    }

    private def put_file(path: Path, f: Path => Unit): Unit =
      run_sftp("put -p local " + sftp_path(path),
        init = dir => f(dir + Path.explode("local")))

    override def read_file(path: Path, local_path: Path): Unit =
      get_file(path, Isabelle_System.copy_file(_, local_path))
    override def read_bytes(path: Path): Bytes =
      get_file(path, Bytes.read)
    override def read(path: Path): String =
      get_file(path, File.read)

    override def write_file(path: Path, local_path: Path): Unit =
      put_file(path, Isabelle_System.copy_file(local_path, _))
    override def write_bytes(path: Path, bytes: Bytes): Unit =
      put_file(path, Bytes.write(_, bytes))
    override def write(path: Path, text: String): Unit =
      put_file(path, File.write(_, text))


    /* tmp dirs */

    override def rm_tree(dir: Path): Unit =
      execute("rm -r -f " + bash_path(dir)).check

    override def tmp_dir(): Path =
      Path.explode(execute("mktemp -d /tmp/ssh-XXXXXXXXXXXX").check.out)

    override def with_tmp_dir[A](body: Path => A): A = {
      val path = tmp_dir()
      try { body(path) } finally { rm_tree(path) }
    }


    /* open server on remote host */

    def open_server(
      remote_port: Int = 0,
      remote_host: String = "localhost",
      local_port: Int = 0,
      local_host: String = "localhost",
      ssh_close: Boolean = false
    ): Server = {
      val forward_host = local_host
      val forward_port = if (local_port > 0) local_port else Isabelle_System.local_port()
      val forward = List(forward_host, forward_port, remote_host, remote_port).mkString(":")
      val forward_option = "-L " + Bash.string(forward)

      val cancel: () => Unit =
        if (control_path.nonEmpty) {
          run_ssh(opts = forward_option + " -O forward").check
          () => run_ssh(opts = forward_option + " -O cancel")  // permissive
        }
        else {
          val result = Synchronized[Exn.Result[Boolean]](Exn.Res(false))
          val thread = Isabelle_Thread.fork("ssh_server") {
            val opts =
              forward_option +
                " " + Config.option("SessionType", "none") +
                " " + Config.option("PermitLocalCommand", true) +
                " " + Config.option("LocalCommand", "pwd")
            try {
              Isabelle_System.bash(make_command(opts = opts, args_host = true),
                progress_stdout = _ => result.change(_ => Exn.Res(true))).check
            }
            catch { case exn: Throwable => result.change(_ => Exn.Exn(exn)) }
          }
          result.guarded_access {
            case res@Exn.Res(ok) => if (ok) Some((), res) else None
            case Exn.Exn(exn) => throw exn
          }
          () => thread.interrupt()
        }

      val shutdown_hook =
        Isabelle_System.create_shutdown_hook { cancel() }

      new Server(forward_host, forward_port, ssh) {
        override def toString: String = forward
        override def close(): Unit = {
          cancel()
          Isabelle_System.remove_shutdown_hook(shutdown_hook)
          if (ssh_close) ssh.close()
        }
      }
    }
  }


  /* server port forwarding */

  def open_server(
    options: Options,
    host: String,
    port: Int = 0,
    user: String = "",
    user_home: String = "",
    remote_port: Int = 0,
    remote_host: String = "localhost",
    local_port: Int = 0,
    local_host: String = "localhost"
  ): Server = {
    val ssh = open_session(options, host, port = port, user = user, user_home = user_home)
    try {
      ssh.open_server(remote_port = remote_port, remote_host = remote_host,
        local_port = local_port, local_host = local_host, ssh_close = true)
    }
    catch { case exn: Throwable => ssh.close(); throw exn }
  }

  def local_server(port: Int = 0, host: String = "localhost"): Server =
    new Local_Server(host, port)

  val no_server: Server = new No_Server

  class Server private[SSH](
    val host: String,
    val port: Int,
    val ssh_system: System
  ) extends AutoCloseable {
    def defined: Boolean = host.nonEmpty && port > 0
    override def close(): Unit = ()
  }

  class Local_Server private[SSH](host: String, port: Int)
  extends Server(host, port, Local) {
    override def toString: String = if_proper(host, host + ":") + port
  }

  class No_Server extends Server("", 0, Local) {
    override def toString: String = "0"
  }


  /* system operations */

  def open_system(
    options: Options,
    host: String,
    port: Int = 0,
    user: String = "",
    user_home: String = ""
  ): System = {
    if (is_local(host)) {
      if (user_home.isEmpty) Local
      else error("Illegal user home for local host")
    }
    else open_session(options, host = host, port = port, user = user, user_home = user_home)
  }

  trait System extends AutoCloseable {
    def ssh_session: Option[Session]
    def is_local: Boolean = ssh_session.isEmpty

    def home: String = ""
    def user_home: String = ""

    def close(): Unit = ()

    override def toString: String = LOCAL
    def print: String = ""
    def hg_url: String = ""
    def client_command: String = ""

    def rsync_prefix: String = ""
    def rsync_path(path: Path): String = rsync_prefix + expand_path(path).implode

    def find_path[A](start: Path, detect: Path => Option[A]): Option[A] = {
      @tailrec def find(root: Path): Option[A] =
        detect(root) match {
          case None => if (root.is_root) None else find(root + Path.parent)
          case some => some
        }

      find(expand_path(start))
    }

    def expand_path(path: Path): Path = path.expand
    def absolute_path(path: Path): Path = path.absolute
    def bash_path(path: Path): String = File.bash_path(path)
    def is_dir(path: Path): Boolean = path.is_dir
    def is_file(path: Path): Boolean = path.is_file
    def eq_file(path1: Path, path2: Path): Boolean = File.eq(path1, path2)
    def delete(path: Path): Unit = path.file.delete
    def restrict(path: Path): Unit = File.restrict(path)
    def set_executable(path: Path, reset: Boolean = false): Unit =
      File.set_executable(path, reset = reset)
    def make_directory(path: Path): Path = Isabelle_System.make_directory(path)
    def rm_tree(dir: Path): Unit = Isabelle_System.rm_tree(dir)
    def tmp_dir(): Path = File.path(Isabelle_System.tmp_dir("tmp"))
    def with_tmp_dir[A](body: Path => A): A = Isabelle_System.with_tmp_dir("tmp")(body)
    def read_dir(path: Path): List[String] = File.read_dir(path)
    def copy_file(path1: Path, path2: Path): Unit = Isabelle_System.copy_file(path1, path2)
    def read_file(path1: Path, path2: Path): Unit = Isabelle_System.copy_file(path1, path2)
    def read_bytes(path: Path): Bytes = Bytes.read(path)
    def read(path: Path): String = File.read(path)
    def write_file(path1: Path, path2: Path): Unit = Isabelle_System.copy_file(path2, path1)
    def write_bytes(path: Path, bytes: Bytes): Unit = Bytes.write(path, bytes)
    def write(path: Path, text: String): Unit = File.write(path, text)

    def execute(command: String,
        progress_stdout: String => Unit = (_: String) => (),
        progress_stderr: String => Unit = (_: String) => (),
        redirect: Boolean = false,
        settings: Boolean = true,
        strict: Boolean = true): Process_Result =
      Isabelle_System.bash(command,
        progress_stdout = progress_stdout,
        progress_stderr = progress_stderr,
        redirect = redirect,
        env = if (settings) Isabelle_System.settings() else null,
        strict = strict)

    def new_directory(path: Path): Path =
      if (is_dir(path)) error("Directory already exists: " + absolute_path(path))
      else make_directory(path)

    def download_file(url_name: String, file: Path, progress: Progress = new Progress): Unit =
      Isabelle_System.download_file(url_name, file, progress = progress)

    def isabelle_platform: Isabelle_Platform = Isabelle_Platform()

    def isabelle_platform_family: Platform.Family =
      Platform.Family.parse(isabelle_platform.ISABELLE_PLATFORM_FAMILY)
  }

  object Local extends System {
    override def ssh_session: Option[Session] = None
  }
}
