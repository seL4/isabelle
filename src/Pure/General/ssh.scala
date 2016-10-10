/*  Title:      Pure/General/ssh.scala
    Author:     Makarius

SSH client based on JSch (see also http://www.jcraft.com/jsch/examples).
*/

package isabelle


import com.jcraft.jsch.{JSch, Logger => JSch_Logger, Session => JSch_Session,
  OpenSSHConfig, UserInfo, ChannelExec, ChannelSftp}


object SSH
{
  /* init */

  def init(config_dir: Path = Path.explode("~/.ssh"),
    config_file: Path = Path.explode("~/.ssh/config"),
    identity_files: List[Path] =
      List("~/.ssh/id_dsa", "~/.ssh/id_ecdsa", "~/.ssh/id_rsa").map(Path.explode(_))): SSH =
  {
    if (!config_dir.is_dir) error("Bad ssh config directory: " + config_dir)

    val jsch = new JSch

    if (config_file.is_file)
      jsch.setConfigRepository(OpenSSHConfig.parseFile(File.platform_path(config_file)))

    val known_hosts = config_dir + Path.explode("known_hosts")
    if (!known_hosts.is_file) known_hosts.file.createNewFile
    jsch.setKnownHosts(File.platform_path(known_hosts))

    for (identity_file <- identity_files if identity_file.is_file)
      jsch.addIdentity(File.platform_path(identity_file))

    new SSH(jsch)
  }


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


  /* session */

  class Session private[SSH](val session: JSch_Session)
  {
    override def toString: String =
      (if (session.getUserName == null) "" else session.getUserName + "@") +
      (if (session.getHost == null) "" else session.getHost) +
      (if (session.getPort == 22) "" else ":" + session.getPort) +
      (if (session.isConnected) "" else " (disconnected)")

    def close { session.disconnect }

    def channel_exec: ChannelExec =
      session.openChannel("exec").asInstanceOf[ChannelExec]

    def channel_sftp: ChannelSftp =
      session.openChannel("sftp").asInstanceOf[ChannelSftp]
  }

  object No_User_Info extends UserInfo
  {
    def getPassphrase: String = null
    def getPassword: String = null
    def promptPassword(msg: String): Boolean = false
    def promptPassphrase(msg: String): Boolean = false
    def promptYesNo(msg: String): Boolean = false
    def showMessage(msg: String): Unit = Output.writeln(msg)
  }
}

class SSH private(val jsch: JSch)
{
  def open_session(host: String, port: Int = 22, user: String = null,
    connect_timeout: Time = Time.seconds(60),
    compression: Boolean = true): SSH.Session =
  {
    val session = jsch.getSession(user, host, port)

    session.setUserInfo(SSH.No_User_Info)
    session.setConfig("MaxAuthTries", "3")

    if (compression) {
      session.setConfig("compression.s2c", "zlib@openssh.com,zlib,none")
      session.setConfig("compression.c2s", "zlib@openssh.com,zlib,none")
      session.setConfig("compression_level", "9")
    }

    if (connect_timeout.is_zero) session.connect
    else session.connect(connect_timeout.ms.toInt)

    new SSH.Session(session)
  }
}
