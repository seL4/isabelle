/*  Title:      Pure/General/ssh.scala
    Author:     Makarius

SSH client on OpenSSH command-line tools, preferably with connection
multiplexing, but this does not work on Windows.
*/

package isabelle


import java.util.{Map => JMap}
import java.net.ServerSocket


object SSH {
  /* target machine: user@host syntax */

  object Target {
    def parse(s: String): (String, String) = {
      val i = s.indexOf('@')
      if (i <= 0) ("", s)
      else (s.substring(0, i), s.substring(i + 1))
    }

    def unapplySeq(s: String): Option[List[String]] = {
      val (user, host) = parse(s)
      if (host.isEmpty) None else Some(List(user, host))
    }
  }


  /* OpenSSH configuration and command-line */

  // see https://linux.die.net/man/5/ssh_config
  object Config {
    def entry(x: String, y: String): String = x + "=" + y
    def entry(x: String, y: Int): String = entry(x, y.toString)
    def entry(x: String, y: Boolean): String = entry(x, if (y) "yes" else "no")

    def make(options: Options,
      port: Int = 0,
      user: String = "",
      control_master: Boolean = false,
      control_path: String = ""
    ): List[String] = {
      List("BatchMode=yes",
        entry("ConnectTimeout", options.seconds("ssh_connect_timeout").ms.toInt),
        entry("ServerAliveInterval", options.seconds("ssh_alive_interval").ms.toInt),
        entry("ServerAliveCountMax", options.int("ssh_alive_count_max")),
        entry("Compression", options.bool("ssh_compression"))) :::
      (if (port > 0) List(entry("Port", port)) else Nil) :::
      (if (user.nonEmpty) List(entry("User", user)) else Nil) :::
      (if (control_master) List("ControlMaster=yes", "ControlPersist=yes") else Nil) :::
      (if (control_path.nonEmpty) List("ControlPath=" + control_path) else Nil)
    }

    def option(entry: String): String = "-o " + Bash.string(entry)
    def option(x: String, y: String): String = option(entry(x, y))
    def option(x: String, y: Int): String = option(entry(x, y))
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
      if (multiplex) (true, Isabelle_System.tmp_file("ssh_socket", initialized = false).getPath)
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

    def port_suffix: String = if (port > 0) ":" + port else ""
    def user_prefix: String = if (user.nonEmpty) user + "@" else ""

    override def toString: String = user_prefix + host + port_suffix
    override def hg_url: String = "ssh://" + toString + "/"
    override def rsync_prefix: String = user_prefix + host + ":"


    /* local ssh commands */

    def run_command(command: String,
      master: Boolean = false,
      opts: String = "",
      args: String = "",
      progress_stdout: String => Unit = (_: String) => (),
      progress_stderr: String => Unit = (_: String) => (),
      strict: Boolean = true
    ): Process_Result = {
      val config =
        Config.make(options, port = port, user = user,
          control_master = master, control_path = control_path)
      val cmd =
        Config.command(command, config) +
        (if (opts.nonEmpty) " " + opts else "") +
        (if (args.nonEmpty) " -- " + args else "")
      Isabelle_System.bash(cmd, progress_stdout = progress_stdout,
        progress_stderr = progress_stderr, strict = strict)
    }

    def run_sftp(script: String, opts: String = "", args: String = ""): Process_Result = {
      Isabelle_System.with_tmp_file("sftp") { tmp_path =>
        File.write(tmp_path, script)
        val opts1 = "-b " + File.bash_path(tmp_path) + (if (opts.nonEmpty) " " + opts else "")
        val args1 = Bash.string(host) + (if (args.nonEmpty) " " + args else "")
        run_command("sftp", opts = opts1, args = args1)
      }
    }

    def run_ssh(master: Boolean = false, opts: String = "", args: String = ""): Process_Result = {
      val args1 = Bash.string(host) + (if (args.nonEmpty) " " + args else "")
      run_command("ssh", master = master, opts = opts, args = args1)
    }

    def run_scp(opts: String = "", args: String = ""): Process_Result = {
      val opts1 = "-s -p -q" + (if (opts.nonEmpty) " " + opts else "")
      run_command("scp", opts = opts1, args = args)
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

    val settings: JMap[String, String] = JMap.of("HOME", user_home, "USER_HOME", user_home)

    override def close(): Unit = {
      if (control_path.nonEmpty) run_ssh(opts = "-O exit").check
    }


    /* remote commands */

    override def execute(cmd_line: String,
      progress_stdout: String => Unit = (_: String) => (),
      progress_stderr: String => Unit = (_: String) => (),
      settings: Boolean = true,
      strict: Boolean = true
    ): Process_Result = {
      val args1 = Bash.string(host) + " " + Bash.string("export USER_HOME=\"$HOME\"\n" + cmd_line)
      run_command("ssh", args = args1, progress_stdout = progress_stdout,
        progress_stderr = progress_stderr, strict = strict)
    }

    override lazy val isabelle_platform: Isabelle_Platform = Isabelle_Platform(ssh = Some(ssh))


    /* remote file-system */

    override def expand_path(path: Path): Path = path.expand_env(settings)
    def remote_path(path: Path): String = expand_path(path).implode

    override def bash_path(path: Path): String = Bash.string(remote_path(path))
    def sftp_path(path: Path): String = sftp_string(remote_path(path))

    def rm(path: Path): Unit = run_sftp("rm " + sftp_path(path)).check

    override def is_dir(path: Path): Boolean = run_ssh(args = "test -d " + bash_path(path)).ok
    override def is_file(path: Path): Boolean = run_ssh(args = "test -f " + bash_path(path)).ok

    override def make_directory(path: Path): Path = {
      if (!execute("mkdir -p " + bash_path(path)).ok) {
        error("Failed to create directory: " + quote(remote_path(path)))
      }
      path
    }

    def read_dir(path: Path): List[String] =
      run_sftp("ls -1 -a " + sftp_path(path)).check.out_lines.flatMap(s =>
        if (s == "." || s == ".." || s.endsWith("/.") || s.endsWith("/..")) None
        else Some(Library.perhaps_unprefix("./", s)))

    override def read_file(path: Path, local_path: Path): Unit =
      run_scp(args = Bash.string(host + ":" + remote_path(path)) + " " +
        File.bash_platform_path(local_path)).check

    override def read_bytes(path: Path): Bytes =
      Isabelle_System.with_tmp_file("scp") { local_path =>
        read_file(path, local_path)
        Bytes.read(local_path)
      }

    override def read(path: Path): String = read_bytes(path).text

    override def write_file(path: Path, local_path: Path): Unit =
      run_scp(args = File.bash_platform_path(local_path) + " " +
        Bash.string(host + ":" + remote_path(path))).check

    def write_bytes(path: Path, bytes: Bytes): Unit =
      Isabelle_System.with_tmp_file("scp") { local_path =>
        Bytes.write(local_path, bytes)
        write_file(path, local_path)
      }

    def write(path: Path, text: String): Unit = write_bytes(path, Bytes(text))


    /* tmp dirs */

    def rm_tree(dir: Path): Unit = rm_tree(remote_path(dir))

    def rm_tree(remote_dir: String): Unit =
      execute("rm -r -f " + Bash.string(remote_dir)).check

    def tmp_dir(): String =
      execute("mktemp -d -t tmp.XXXXXXXXXX").check.out

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

  trait System extends AutoCloseable {
    def close(): Unit = ()

    def hg_url: String = ""

    def rsync_prefix: String = ""
    def rsync_path(path: Path): String = rsync_prefix + expand_path(path).implode

    def expand_path(path: Path): Path = path.expand
    def bash_path(path: Path): String = File.bash_path(path)
    def is_dir(path: Path): Boolean = path.is_dir
    def is_file(path: Path): Boolean = path.is_file
    def make_directory(path: Path): Path = Isabelle_System.make_directory(path)
    def with_tmp_dir[A](body: Path => A): A = Isabelle_System.with_tmp_dir("tmp")(body)
    def read_file(path1: Path, path2: Path): Unit = Isabelle_System.copy_file(path1, path2)
    def write_file(path1: Path, path2: Path): Unit = Isabelle_System.copy_file(path2, path1)
    def read_bytes(path: Path): Bytes = Bytes.read(path)
    def read(path: Path): String = File.read(path)

    def execute(command: String,
        progress_stdout: String => Unit = (_: String) => (),
        progress_stderr: String => Unit = (_: String) => (),
        settings: Boolean = true,
        strict: Boolean = true): Process_Result =
      Isabelle_System.bash(command,
        progress_stdout = progress_stdout,
        progress_stderr = progress_stderr,
        env = if (settings) Isabelle_System.settings() else null,
        strict = strict)

    def isabelle_platform: Isabelle_Platform = Isabelle_Platform()
  }

  object Local extends System
}
