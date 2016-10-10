/*  Title:      Pure/General/ssh.scala
    Author:     Makarius

SSH client based on JSch (see also http://www.jcraft.com/jsch/examples).
*/

package isabelle


import java.io.{InputStream, OutputStream}

import scala.collection.JavaConversions

import com.jcraft.jsch.{JSch, Logger => JSch_Logger, Session => JSch_Session,
  OpenSSHConfig, UserInfo, Channel => JSch_Channel, ChannelExec, ChannelSftp, SftpATTRS}


object SSH
{
  /* init */

  def init(options: Options): SSH =
  {
    val config_dir = Path.explode(options.string("ssh_config_dir"))
    if (!config_dir.is_dir) error("Bad ssh config directory: " + config_dir)

    val jsch = new JSch

    val config_file = Path.explode(options.string("ssh_config_file"))
    if (config_file.is_file)
      jsch.setConfigRepository(OpenSSHConfig.parseFile(File.platform_path(config_file)))

    val known_hosts = config_dir + Path.explode("known_hosts")
    if (!known_hosts.is_file) known_hosts.file.createNewFile
    jsch.setKnownHosts(File.platform_path(known_hosts))

    val identity_files =
      Library.space_explode(':', options.string("ssh_identity_files")).map(Path.explode(_))
    for (identity_file <- identity_files if identity_file.is_file)
      jsch.addIdentity(File.platform_path(identity_file))

    new SSH(options, jsch)
  }

  def connect_timeout(options: Options): Int =
    options.seconds("ssh_connect_timeout").ms.toInt


  /* logging */

  def logging(verbose: Boolean = true, debug: Boolean = false)
  {
    JSch.setLogger(if (verbose) new Logger(debug) else null)
  }

  private class Logger(debug: Boolean) extends JSch_Logger
  {
    def isEnabled(level: Int): Boolean = level != JSch_Logger.DEBUG || debug

    def log(level: Int, msg: String)
    {
      level match {
        case JSch_Logger.ERROR | JSch_Logger.FATAL => Output.error_message(msg)
        case JSch_Logger.WARN => Output.warning(msg)
        case _ => Output.writeln(msg)
      }
    }
  }


  /* user info */

  object No_User_Info extends UserInfo
  {
    def getPassphrase: String = null
    def getPassword: String = null
    def promptPassword(msg: String): Boolean = false
    def promptPassphrase(msg: String): Boolean = false
    def promptYesNo(msg: String): Boolean = false
    def showMessage(msg: String): Unit = Output.writeln(msg)
  }


  /* channel */

  class Channel[C <: JSch_Channel] private[SSH](val session: Session,
    val kind: String, val channel_options: Options, val channel: C)
  {
    override def toString: String = kind + " " + session.toString

    def close { channel.disconnect }
  }


  /* exec channel */

  class Exec private[SSH](
    session: Session, kind: String, channel_options: Options, channel: ChannelExec)
    extends Channel[ChannelExec](session, kind, channel_options, channel)
  {
    def kill(signal: String) { channel.sendSignal(signal) }
  }


  /* Sftp channel */

  type Attrs = SftpATTRS

  sealed case class Dir_Entry(name: String, attrs: Attrs)
  {
    def is_file: Boolean = attrs.isReg
    def is_dir: Boolean = attrs.isDir
  }

  class Sftp private[SSH](
    session: Session, kind: String, channel_options: Options, channel: ChannelSftp)
    extends Channel[ChannelSftp](session, kind, channel_options, channel)
  {
    def home: String = channel.getHome()

    def chmod(permissions: Int, remote_path: String) { channel.chmod(permissions, remote_path) }
    def mv(remote_path1: String, remote_path2: String): Unit =
      channel.rename(remote_path1, remote_path2)
    def rm(remote_path: String) { channel.rm(remote_path) }
    def mkdir(remote_path: String) { channel.mkdir(remote_path) }
    def rmdir(remote_path: String) { channel.rmdir(remote_path) }

    def stat(remote_path: String): Dir_Entry =
      Dir_Entry(remote_path, channel.stat(remote_path))

    def read_dir(remote_path: String): List[Dir_Entry] =
    {
      val dir = channel.ls(remote_path)
      (for {
        i <- (0 until dir.size).iterator
        a = dir.get(i).asInstanceOf[AnyRef]
        name = Untyped.get[String](a, "filename")
        attrs = Untyped.get[Attrs](a, "attrs")
        if name != "." && name != ".."
      } yield Dir_Entry(name, attrs)).toList
    }

    def find_files(remote_path: String, pred: Dir_Entry => Boolean = _ => true): List[Dir_Entry] =
    {
      def find(dir: String): List[Dir_Entry] =
        read_dir(dir).flatMap(entry =>
          {
            val file = dir + "/" + entry.name
            if (entry.is_dir) find(file)
            else if (pred(entry)) List(entry.copy(name = file))
            else Nil
          })
      find(remote_path)
    }

    def open_input(remote_path: String): InputStream = channel.get(remote_path)
    def open_output(remote_path: String): OutputStream = channel.put(remote_path)

    def read_file(remote_path: String, local_path: Path): Unit =
      channel.get(remote_path, File.platform_path(local_path))
    def read_bytes(remote_path: String): Bytes =
      using(open_input(remote_path))(Bytes.read_stream(_))
    def read(remote_path: String): String =
      using(open_input(remote_path))(File.read_stream(_))

    def write_file(remote_path: String, local_path: Path): Unit =
      channel.put(File.platform_path(local_path), remote_path)
    def write_bytes(remote_path: String, bytes: Bytes): Unit =
      using(open_output(remote_path))(bytes.write_stream(_))
    def write(remote_path: String, text: String): Unit =
      using(open_output(remote_path))(stream => Bytes(text).write_stream(stream))
  }


  /* session */

  class Session private[SSH](val session_options: Options, val session: JSch_Session)
  {
    override def toString: String =
      (if (session.getUserName == null) "" else session.getUserName + "@") +
      (if (session.getHost == null) "" else session.getHost) +
      (if (session.getPort == 22) "" else ":" + session.getPort) +
      (if (session.isConnected) "" else " (disconnected)")

    def close { session.disconnect }

    def exec(command: String, options: Options = session_options): Exec =
    {
      val kind = "exec"
      val channel = session.openChannel(kind).asInstanceOf[ChannelExec]
      channel.setCommand(command)

      channel.connect(connect_timeout(options))
      new Exec(this, kind, options, channel)
    }

    def sftp(options: Options = session_options): Sftp =
    {
      val kind = "sftp"
      val channel = session.openChannel(kind).asInstanceOf[ChannelSftp]

      channel.connect(connect_timeout(options))
      new Sftp(this, kind, options, channel)
    }
  }
}

class SSH private(val options: Options, val jsch: JSch)
{
  def open_session(host: String, port: Int = 22, user: String = null): SSH.Session =
  {
    val session = jsch.getSession(user, host, port)

    session.setUserInfo(SSH.No_User_Info)
    session.setConfig("MaxAuthTries", "3")

    if (options.bool("ssh_compression")) {
      session.setConfig("compression.s2c", "zlib@openssh.com,zlib,none")
      session.setConfig("compression.c2s", "zlib@openssh.com,zlib,none")
      session.setConfig("compression_level", "9")
    }

    session.connect(SSH.connect_timeout(options))
    new SSH.Session(options, session)
  }
}
