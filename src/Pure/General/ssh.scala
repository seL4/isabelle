/*  Title:      Pure/General/ssh.scala
    Author:     Makarius

SSH client on OpenSSH command-line tools, preferably with connection
multiplexing, but this does not work on Windows.
*/

package isabelle


import java.util.{Map => JMap}
import java.io.{File => JFile}


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


  /* open session */

  def open_session(
    options: Options,
    host: String,
    port: Int = 0,
    user: String = ""
  ): Session = {
    val multiplex = options.bool("ssh_multiplexing") && !Platform.is_windows
    val (control_master, control_path) =
      if (multiplex) (true, Isabelle_System.tmp_file("ssh", initialized = false).getPath)
      else (false, "")
    new Session(options, host, port, user, control_master, control_path)
  }

  class Session private[SSH](
    val options: Options,
    val host: String,
    val port: Int,
    val user: String,
    control_master: Boolean,
    val control_path: String
  ) extends System {
    ssh =>

    override def is_local: Boolean = false

    def port_suffix: String = if (port > 0) ":" + port else ""
    def user_prefix: String = if (user.nonEmpty) user + "@" else ""

    override def toString: String = user_prefix + host + port_suffix
    override def print: String = " (ssh " + toString + ")"
    override def hg_url: String = "ssh://" + toString + "/"
    override def client_command: String =
      SSH.client_command(port = port, control_path = control_path)
    override def rsync_prefix: String = user_prefix + host + ":"


    /* local ssh commands */

    def run_command(command: String,
      master: Boolean = false,
      opts: String = "",
      args: String = "",
      cwd: JFile = null,
      redirect: Boolean = false,
      progress_stdout: String => Unit = (_: String) => (),
      progress_stderr: String => Unit = (_: String) => (),
      strict: Boolean = true
    ): Process_Result = {
      val config =
        Config.make(options, port = port, user = user,
          control_master = master, control_path = control_path)
      val cmd =
        Config.command(command, config) +
        if_proper(opts, " " + opts) +
        if_proper(args, " -- " + args)
      Isabelle_System.bash(cmd, cwd = cwd,
        redirect = redirect,
        progress_stdout = progress_stdout,
        progress_stderr = progress_stderr,
        strict = strict)
    }

    def run_sftp(
      script: String,
      init: Path => Unit = _ => (),
      exit: Path => Unit = _ => ()
    ): Process_Result = {
      Isabelle_System.with_tmp_dir("ssh") { dir =>
        init(dir)
        File.write(dir + Path.explode("script"), script)
        val result =
          run_command("sftp", opts = "-b script", args = Bash.string(host), cwd = dir.file).check
        exit(dir)
        result
      }
    }

    def run_ssh(master: Boolean = false, opts: String = "", args: String = ""): Process_Result = {
      val args1 = Bash.string(host) + if_proper(args, " " + args)
      run_command("ssh", master = master, opts = opts, args = args1)
    }


    /* init and exit */

    val user_home: String = {
      run_ssh(master = control_master, args = "printenv HOME \";\" printenv SHELL").check.out_lines
      match {
        case List(user_home, shell) =>
          if (shell.endsWith("/bash")) user_home
          else {
            error("Bad SHELL for " + quote(toString) + " -- expected GNU bash, but found " + shell)
          }
        case _ => error("Malformed remote environment for " + quote(toString))
      }
    }

    val settings: Isabelle_System.Settings =
      (name: String) => if (name == "HOME" || name == "USER_HOME") user_home else ""

    override def close(): Unit = {
      if (control_path.nonEmpty) run_ssh(opts = "-O exit").check
    }


    /* remote commands */

    override def execute(cmd_line: String,
      progress_stdout: String => Unit = (_: String) => (),
      progress_stderr: String => Unit = (_: String) => (),
      redirect: Boolean = false,
      settings: Boolean = true,
      strict: Boolean = true
    ): Process_Result = {
      run_command("ssh",
        args = Bash.string(host) + " " + Bash.string(cmd_line),
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
      if (path1.is_absolute) path1 else Path.explode(user_home) + path1
    }

    def remote_path(path: Path): String = expand_path(path).implode

    override def bash_path(path: Path): String = Bash.string(remote_path(path))
    def sftp_path(path: Path): String = sftp_string(remote_path(path))

    override def is_dir(path: Path): Boolean = run_ssh(args = "test -d " + bash_path(path)).ok
    override def is_file(path: Path): Boolean = run_ssh(args = "test -f " + bash_path(path)).ok

    override def delete(path: Path): Unit = {
      val cmd = if (is_dir(path)) "rmdir" else if (is_file(path)) "rm" else ""
      if (cmd.nonEmpty) run_sftp(cmd + " " + sftp_path(path))
    }

    override def set_executable(path: Path, flag: Boolean): Unit =
      if (!execute("chmod a" + (if (flag) "+" else "-") + "x " + bash_path(path)).ok) {
        error("Failed to change executable status of " + quote(remote_path(path)))
      }

    override def make_directory(path: Path): Path = {
      if (!execute("mkdir -p " + bash_path(path)).ok) {
        error("Failed to create directory: " + quote(remote_path(path)))
      }
      path
    }

    override def copy_file(src: Path, dst: Path): Unit = {
      val direct = if (is_dir(dst)) "/." else ""
      if (!execute("cp -a " + bash_path(src) + " " + bash_path(dst) + direct).ok) {
        error("Failed to copy file " + expand_path(src) + " to " +
          expand_path(dst) + " (ssh " + toString + ")")
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

    override def rm_tree(dir: Path): Unit = rm_tree(remote_path(dir))

    def rm_tree(remote_dir: String): Unit =
      execute("rm -r -f " + Bash.string(remote_dir)).check

    def tmp_dir(): String =
      execute("mktemp -d /tmp/ssh-XXXXXXXXXXXX").check.out

    override def with_tmp_dir[A](body: Path => A): A = {
      val remote_dir = tmp_dir()
      try { body(Path.explode(remote_dir)) }
      finally { rm_tree(remote_dir) }
    }


    /* port forwarding */

    def port_forwarding(
      remote_port: Int,
      remote_host: String = "localhost",
      local_port: Int = 0,
      local_host: String = "localhost",
      ssh_close: Boolean = false
    ): Port_Forwarding = {
      val port = if (local_port > 0) local_port else Isabelle_System.local_port()

      val forward = List(local_host, port, remote_host, remote_port).mkString(":")
      val forward_option = "-L " + Bash.string(forward)

      val cancel: () => Unit =
        if (control_path.nonEmpty) {
          run_ssh(opts = forward_option + " -O forward").check
          () => run_ssh(opts = forward_option + " -O cancel")  // permissive
        }
        else {
          val result = Synchronized[Exn.Result[Boolean]](Exn.Res(false))
          val thread = Isabelle_Thread.fork("port_forwarding") {
            val opts =
              forward_option +
                " " + Config.option("SessionType", "none") +
                " " + Config.option("PermitLocalCommand", true) +
                " " + Config.option("LocalCommand", "pwd")
            try {
              run_command("ssh", opts = opts, args = Bash.string(host),
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

      new Port_Forwarding(host, port, remote_host, remote_port) {
        override def toString: String = forward
        override def close(): Unit = {
          cancel()
          Isabelle_System.remove_shutdown_hook(shutdown_hook)
          if (ssh_close) ssh.close()
        }
      }
    }
  }

  abstract class Port_Forwarding private[SSH](
    val host: String,
    val port: Int,
    val remote_host: String,
    val remote_port: Int
  ) extends AutoCloseable


  /* system operations */

  def open_system(
    options: Options,
    host: String,
    port: Int = 0,
    user: String = ""
  ): System = {
    if (host.isEmpty) Local
    else open_session(options, host = host, port = port, user = user)
  }

  trait System extends AutoCloseable {
    def is_local: Boolean

    def close(): Unit = ()

    override def toString: String = "SSH.Local"
    def print: String = ""
    def hg_url: String = ""
    def client_command: String = ""

    def rsync_prefix: String = ""
    def rsync_path(path: Path): String = rsync_prefix + expand_path(path).implode

    def expand_path(path: Path): Path = path.expand
    def absolute_path(path: Path): Path = path.absolute
    def bash_path(path: Path): String = File.bash_path(path)
    def is_dir(path: Path): Boolean = path.is_dir
    def is_file(path: Path): Boolean = path.is_file
    def delete(path: Path): Unit = path.file.delete
    def set_executable(path: Path, flag: Boolean): Unit = File.set_executable(path, flag)
    def make_directory(path: Path): Path = Isabelle_System.make_directory(path)
    def rm_tree(dir: Path): Unit = Isabelle_System.rm_tree(dir)
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

    def isabelle_platform_family: Platform.Family.Value =
      Platform.Family.parse(isabelle_platform.ISABELLE_PLATFORM_FAMILY)
  }

  object Local extends System {
    override def is_local: Boolean = true
  }
}
