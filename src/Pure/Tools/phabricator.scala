/*  Title:      Pure/Tools/phabricator.scala
    Author:     Makarius

Support for Phabricator server, notably for Ubuntu 18.04 LTS.

See also:
  - https://www.phacility.com/phabricator
  - https://secure.phabricator.com/book/phabricator
*/

package isabelle


import scala.util.matching.Regex


object Phabricator
{
  /** defaults **/

  /* required packages */

  val packages: List[String] =
    Build_Docker.packages :::
    List(
      // https://secure.phabricator.com/source/phabricator/browse/master/scripts/install/install_ubuntu.sh 15e6e2adea61
      "git", "mysql-server", "apache2", "libapache2-mod-php", "php", "php-mysql",
      "php-gd", "php-curl", "php-apcu", "php-cli", "php-json", "php-mbstring",
      // more packages
      "php-zip", "python-pygments", "ssh")


  /* global system resources */

  val www_user = "www-data"

  val daemon_user = "phabricator"

  val sshd_config = Path.explode("/etc/ssh/sshd_config")


  /* installation parameters */

  val default_name = "vcs"

  def phabricator_name(name: String = "", ext: String = ""): String =
    "phabricator" + (if (name.isEmpty) "" else "-" + name) + (if (ext.isEmpty) "" else "." + ext)

  def isabelle_phabricator_name(name: String = "", ext: String = ""): String =
    "isabelle-" + phabricator_name(name = name, ext = ext)

  def default_root(name: String): Path =
    Path.explode("/var/www") + Path.basic(phabricator_name(name = name))

  def default_repo(name: String): Path = default_root(name) + Path.basic("repo")

  val default_mailers: Path = Path.explode("mailers.json")

  val default_system_port = 22
  val alternative_system_port = 222
  val default_server_port = 2222



  /** global configuration **/

  val global_config = Path.explode("/etc/" + isabelle_phabricator_name(ext = "conf"))

  def global_config_script(
    header: Boolean = false,
    init: String = "",
    body: String = "",
    exit: String = ""): String =
  {
    (if (header) "#!/bin/bash\n" else "") +
"""
{""" + (if (init.nonEmpty) "\n" + Library.prefix_lines("  ", init) else "") + """
  while { unset REPLY; read -r; test "$?" = 0 -o -n "$REPLY"; }
  do
    NAME="$(echo "$REPLY" | cut -d: -f1)"
    ROOT="$(echo "$REPLY" | cut -d: -f2)"
""" + Library.prefix_lines("    ", body) + """
  done""" +
    (if (exit.nonEmpty) "\n" + Library.prefix_lines("  ", exit) else "") + """
} < """ + File.bash_path(global_config) + """
"""
  }

  sealed case class Config(name: String, root: Path)
  {
    def home: Path = root + Path.explode(phabricator_name())

    def execute(command: String): Process_Result =
      Isabelle_System.bash("bin/" + command, cwd = home.file, redirect = true).check
  }

  def read_config(): List[Config] =
  {
    if (global_config.is_file) {
      for (entry <- Library.trim_split_lines(File.read(global_config)) if entry.nonEmpty)
      yield {
        space_explode(':', entry) match {
          case List(name, root) => Config(name, Path.explode(root))
          case _ => error("Malformed config file " + global_config + "\nentry " + quote(entry))
        }
      }
    }
    else Nil
  }

  def write_config(configs: List[Config])
  {
    File.write(global_config,
      configs.map(config => config.name + ":" + config.root.implode).mkString("", "\n", "\n"))
  }

  def get_config(name: String): Config =
    read_config().find(config => config.name == name) getOrElse
      error("Bad Isabelle/Phabricator installation " + quote(name))



  /** command-line tools **/

  /* Isabelle tool wrapper */

  val isabelle_tool1 =
    Isabelle_Tool("phabricator", "invoke command-line tool within Phabricator home directory", args =>
    {
      var list = false
      var name = default_name

      val getopts =
        Getopts("""
Usage: isabelle phabricator [OPTIONS] COMMAND [ARGS...]

  Options are:
    -l           list available Phabricator installations
    -n NAME      Phabricator installation name (default: """ + quote(default_name) + """)

  Invoke a command-line tool within the home directory of the named
  Phabricator installation.
""",
          "l" -> (_ => list = true),
          "n:" -> (arg => name = arg))

      val more_args = getopts(args)
      if (more_args.isEmpty && !list) getopts.usage()

      val progress = new Console_Progress

      if (list) {
        for (config <- read_config()) {
          progress.echo("phabricator " + quote(config.name) + " root " + config.root)
        }
      }

      val config = get_config(name)

      val result = progress.bash(Bash.strings(more_args), cwd = config.home.file, echo = true)
      if (!result.ok) error("Return code: " + result.rc.toString)
    })



  /** setup **/

  def user_setup(name: String, description: String, ssh_setup: Boolean = false)
  {
    if (!Linux.user_exists(name)) {
      Linux.user_add(name, description = description, system = true, ssh_setup = ssh_setup)
    }
    else if (Linux.user_description(name) != description) {
      error("User " + quote(name) + " already exists --" +
        " for Phabricator it should have the description:\n  " + quote(description))
    }
  }

  def phabricator_setup(
    name: String = default_name,
    root: String = "",
    repo: String = "",
    package_update: Boolean = false,
    progress: Progress = No_Progress)
  {
    /* system environment */

    Linux.check_system_root()

    progress.echo("System packages ...")

    if (package_update) {
      Linux.package_update(progress = progress)
      Linux.check_reboot_required()
    }

    Linux.package_install(packages, progress = progress)
    Linux.check_reboot_required()


    /* users */

    if (name.contains((c: Char) => !(Symbol.is_ascii_letter(c) || Symbol.is_ascii_digit(c))) ||
        Set("", "ssh", "phd", daemon_user).contains(name)) {
      error("Bad installation name: " + quote(name))
    }

    user_setup(daemon_user, "Phabricator Daemon User", ssh_setup = true)
    user_setup(name, "Phabricator SSH User")


    /* basic installation */

    progress.echo("\nPhabricator installation ...")

    val root_path = if (root.nonEmpty) Path.explode(root) else default_root(name)
    val repo_path = if (repo.nonEmpty) Path.explode(repo) else default_repo(name)

    val configs = read_config()

    for (config <- configs if config.name == name) {
      error("Duplicate Phabricator installation " + quote(name) + " in " + config.root)
    }

    if (!Isabelle_System.bash("mkdir -p " + File.bash_path(root_path)).ok) {
      error("Failed to create root directory " + root_path)
    }

    Isabelle_System.chown(Bash.string(www_user) + ":" + Bash.string(www_user), root_path)
    Isabelle_System.chmod("755", root_path)

    progress.bash(cwd = root_path.file, echo = true,
      script = """
        set -e
        echo "Cloning distribution repositories"
        git clone https://github.com/phacility/libphutil.git
        git clone https://github.com/phacility/arcanist.git
        git clone https://github.com/phacility/phabricator.git
      """).check

    val config = Config(name, root_path)
    write_config(configs ::: List(config))

    config.execute("config set pygments.enabled true")


    /* local repository directory */

    progress.echo("\nRepository hosting setup ...")

    if (!Isabelle_System.bash("mkdir -p " + File.bash_path(repo_path)).ok) {
      error("Failed to create local repository directory " + repo_path)
    }

    Isabelle_System.chown(
      "-R " + Bash.string(daemon_user) + ":" + Bash.string(daemon_user), repo_path)
    Isabelle_System.chmod("755", repo_path)

    config.execute("config set repository.default-local-path " + File.bash_path(repo_path))


    val sudoers_file = Path.explode("/etc/sudoers.d") + Path.basic(isabelle_phabricator_name())
    File.write(sudoers_file,
      www_user + " ALL=(" + daemon_user + ") SETENV: NOPASSWD: /usr/bin/git, /usr/bin/hg, /usr/bin/ssh, /usr/bin/id\n" +
      name + " ALL=(" + daemon_user + ") SETENV: NOPASSWD: /usr/bin/git, /usr/bin/git-upload-pack, /usr/bin/git-receive-pack, /usr/bin/hg, /usr/bin/svnserve, /usr/bin/ssh, /usr/bin/id\n")

    Isabelle_System.chmod("440", sudoers_file)

    config.execute("config set diffusion.ssh-user " + Bash.string(config.name))


    /* MySQL setup */

    progress.echo("\nMySQL setup ...")

    File.write(Path.explode("/etc/mysql/mysql.conf.d/" + phabricator_name(ext = "cnf")),
"""[mysqld]
max_allowed_packet = 32M
innodb_buffer_pool_size = 1600M
local_infile = 0
""")

    Linux.service_restart("mysql")


    def mysql_conf(R: Regex): Option[String] =
      split_lines(File.read(Path.explode("/etc/mysql/debian.cnf"))).collectFirst({ case R(a) => a })

    for (user <- mysql_conf("""^user\s*=\s*(\S*)\s*$""".r)) {
      config.execute("config set mysql.user " + Bash.string(user))
    }

    for (pass <- mysql_conf("""^password\s*=\s*(\S*)\s*$""".r)) {
      config.execute("config set mysql.pass " + Bash.string(pass))
    }

    config.execute("config set storage.default-namespace " +
      Bash.string(phabricator_name(name = name).replace("-", "_")))

    config.execute("config set storage.mysql-engine.max-size 8388608")

    progress.bash("bin/storage upgrade --force", cwd = config.home.file, echo = true).check


    /* PHP setup */

    val php_version =
      Isabelle_System.bash("""php --run 'echo PHP_MAJOR_VERSION . "." . PHP_MINOR_VERSION;'""")
        .check.out

    val php_conf =
      Path.explode("/etc/php") + Path.basic(php_version) +  // educated guess
        Path.explode("apache2/conf.d") +
        Path.basic(isabelle_phabricator_name(ext = "ini"))

    File.write(php_conf,
      "post_max_size = 32M\n" +
      "opcache.validate_timestamps = 0\n" +
      "memory_limit = 512M\n")


    /* Apache setup */

    progress.echo("Apache setup ...")

    val apache_root = Path.explode("/etc/apache2")
    val apache_sites = apache_root + Path.explode("sites-available")

    if (!apache_sites.is_dir) error("Bad Apache sites directory " + apache_sites)

    val server_name = phabricator_name(name = name, ext = "lvh.me")  // alias for "localhost" for testing
    val server_url = "http://" + server_name

    File.write(apache_sites + Path.basic(isabelle_phabricator_name(name = name, ext = "conf")),
"""<VirtualHost *:80>
    ServerName """ + server_name + """
    ServerAdmin webmaster@localhost
    DocumentRoot """ + config.home.implode + """/webroot

    ErrorLog ${APACHE_LOG_DIR}/error.log
    RewriteEngine on
    RewriteRule ^(.*)$  /index.php?__path__=$1  [B,L,QSA]
</VirtualHost>

# vim: syntax=apache ts=4 sw=4 sts=4 sr noet
""")

    Isabelle_System.bash( """
      set -e
      a2enmod rewrite
      a2ensite """ + Bash.string(isabelle_phabricator_name(name = name))).check

    config.execute("config set phabricator.base-uri " + Bash.string(server_url))

    Linux.service_restart("apache2")


    /* PHP daemon */

    progress.echo("PHP daemon setup ...")

    config.execute("config set phd.user " + Bash.string(daemon_user))
    config.execute("config set phd.log-directory /var/tmp/phd/" +
      isabelle_phabricator_name(name = name) + "/log")

    val phd_name = isabelle_phabricator_name(name = "phd")
    val phd_command = Path.explode("/usr/local/bin") + Path.basic(phd_name)

    File.write(phd_command,
      global_config_script(header = true, body = """"$ROOT/phabricator/bin/phd" "$@" """))
    Isabelle_System.chmod("755", phd_command)
    Isabelle_System.chown("root:root", phd_command)

    Linux.service_install(phd_name,
"""[Unit]
Description=PHP daemon manager for Isabelle/Phabricator
After=syslog.target network.target apache2.service mysql.service

[Service]
Type=oneshot
User=""" + daemon_user + """
Group=""" + daemon_user + """
Environment=PATH=/sbin:/usr/sbin:/usr/local/sbin:/usr/local/bin:/usr/bin:/bin
ExecStart=""" + phd_command.implode + """ start --force
ExecStop=""" + phd_command.implode + """ stop
RemainAfterExit=yes

[Install]
WantedBy=multi-user.target
""")


    progress.echo("\nDONE\nWeb configuration via " + server_url)
  }


  /* Isabelle tool wrapper */

  val isabelle_tool2 =
    Isabelle_Tool("phabricator_setup", "setup Phabricator server on Ubuntu Linux", args =>
    {
      var repo = ""
      var package_update = false
      var name = default_name
      var root = ""

      val getopts =
        Getopts("""
Usage: isabelle phabricator_setup [OPTIONS]

  Options are:
    -R DIR       repository directory (default: """ + default_repo("NAME") + """)
    -U           full update of system packages before installation
    -n NAME      Phabricator installation name (default: """ + quote(default_name) + """)
    -r DIR       installation root directory (default: """ + default_root("NAME") + """)

  Install Phabricator as LAMP application (Linux, Apache, MySQL, PHP).

  The installation name (default: """ + quote(default_name) + """) is mapped to a regular
  Unix user; this is relevant for public SSH access.
""",
          "R:" -> (arg => repo = arg),
          "U" -> (_ => package_update = true),
          "n:" -> (arg => name = arg),
          "r:" -> (arg => root = arg))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress

      phabricator_setup(name = name, root = root, repo = repo,
        package_update = package_update, progress = progress)
    })



  /** setup mail **/

  val mailers_template: String =
"""[
  {
    "key": "example.org",
    "type": "smtp",
    "options": {
      "host": "mail.example.org",
      "port": 465,
      "user": "phabricator@example.org",
      "password": "********",
      "protocol": "ssl",
      "message-id": true
    }
  }
]"""

  def phabricator_setup_mail(
    name: String = default_name,
    config_file: Option[Path] = None,
    test_user: String = "",
    progress: Progress = No_Progress)
  {
    Linux.check_system_root()

    val config = get_config(name)
    val default_config_file = config.root + default_mailers

    val mail_config = config_file getOrElse default_config_file

    def setup_mail
    {
      progress.echo("Using mail configuration from " + mail_config)
      config.execute("config set cluster.mailers --stdin < " + File.bash_path(mail_config))

      if (test_user.nonEmpty) {
        progress.echo("Sending test mail to " + quote(test_user))
        progress.bash(cwd = config.home.file, echo = true,
          script = """echo "Test from Phabricator ($(date))" | bin/mail send-test --subject "Test" --to """ +
            Bash.string(test_user)).check
      }
    }

    if (config_file.isEmpty) {
      if (!default_config_file.is_file) {
        File.write(default_config_file, mailers_template)
        Isabelle_System.chmod("600", default_config_file)
      }
      if (File.read(default_config_file) == mailers_template) {
        progress.echo(
"""
Please invoke the tool again, after providing details in
  """ + default_config_file.implode + """

See also section "Mailer: SMTP" in
  https://secure.phabricator.com/book/phabricator/article/configuring_outbound_email
""")
      }
      else setup_mail
    }
    else setup_mail
  }


  /* Isabelle tool wrapper */

  val isabelle_tool3 =
    Isabelle_Tool("phabricator_setup_mail",
      "setup mail for one Phabricator installation", args =>
    {
      var test_user = ""
      var name = default_name
      var config_file: Option[Path] = None

      val getopts =
        Getopts("""
Usage: isabelle phabricator_setup_mail [OPTIONS]

  Options are:
    -T USER      send test mail to Phabricator user
    -f FILE      config file (default: """ + default_mailers + """ within Phabricator root)
    -n NAME      Phabricator installation name (default: """ + quote(default_name) + """)

  Provide mail configuration for existing Phabricator installation.
""",
          "T:" -> (arg => test_user = arg),
          "f:" -> (arg => config_file = Some(Path.explode(arg))),
          "n:" -> (arg => name = arg))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress

      phabricator_setup_mail(name = name, config_file = config_file,
        test_user = test_user, progress = progress)
    })



  /** setup ssh **/

  /* sshd config */

  private val Port = """^\s*Port\s+(\d+)\s*$""".r
  private val No_Port = """^#\s*Port\b.*$""".r
  private val Any_Port = """^#?\s*Port\b.*$""".r

  def conf_ssh_port(port: Int): String =
    if (port == 22) "#Port 22" else "Port " + port

  def read_ssh_port(conf: Path): Int =
  {
    val lines = split_lines(File.read(conf))
    val ports =
      lines.flatMap({
        case Port(Value.Int(p)) => Some(p)
        case No_Port() => Some(22)
        case _ => None
      })
    ports match {
      case List(port) => port
      case Nil => error("Missing Port specification in " + conf)
      case _ => error("Multiple Port specifications in " + conf)
    }
  }

  def write_ssh_port(conf: Path, port: Int): Boolean =
  {
    val old_port = read_ssh_port(conf)
    if (old_port == port) false
    else {
      val lines = split_lines(File.read(conf))
      val lines1 = lines.map({ case Any_Port() => conf_ssh_port(port) case line => line })
      File.write(conf, cat_lines(lines1))
      true
    }
  }


  /* phabricator_setup_ssh */

  def phabricator_setup_ssh(
    server_port: Int = default_server_port,
    system_port: Int = default_system_port,
    test_server: Boolean = false,
    progress: Progress = No_Progress)
  {
    Linux.check_system_root()

    val configs = read_config()

    if (server_port == system_port) {
      error("Port for Phabricator sshd coincides with system port: " + system_port)
    }

    val sshd_conf_system = Path.explode("/etc/ssh/sshd_config")
    val sshd_conf_server = sshd_conf_system.ext(isabelle_phabricator_name())

    val ssh_name = isabelle_phabricator_name(name = "ssh")
    val ssh_command = Path.explode("/usr/local/bin") + Path.basic(ssh_name)

    Linux.service_shutdown(ssh_name)

    val old_system_port = read_ssh_port(sshd_conf_system)
    if (old_system_port != system_port) {
      progress.echo("Reconfigurig system ssh service")
      Linux.service_shutdown("ssh")
      write_ssh_port(sshd_conf_system, system_port)
      Linux.service_start("ssh")
    }

    progress.echo("Configuring " + ssh_name + " service")

    File.write(ssh_command,
      global_config_script(
        header = true,
        body =
"""if [ "$1" = "$NAME" ]
then
  exec "$ROOT/phabricator/bin/ssh-auth" "$@"
fi""",
        exit = "exit 1"))
    Isabelle_System.chmod("755", ssh_command)
    Isabelle_System.chown("root:root", ssh_command)

    File.write(sshd_conf_server,
"""# OpenBSD Secure Shell server for Isabelle/Phabricator
AuthorizedKeysCommand """ + ssh_command.implode + """
AuthorizedKeysCommandUser """ + daemon_user + """
AuthorizedKeysFile none
AllowUsers """ + configs.map(_.name).mkString(" ") + """
Port """ + server_port + """
Protocol 2
PermitRootLogin no
AllowAgentForwarding no
AllowTcpForwarding no
PrintMotd no
PrintLastLog no
PasswordAuthentication no
ChallengeResponseAuthentication no
PidFile /var/run/""" + ssh_name + """.pid
""")

    Linux.service_install(ssh_name,
"""[Unit]
Description=OpenBSD Secure Shell server for Isabelle/Phabricator
After=network.target auditd.service
ConditionPathExists=!/etc/ssh/sshd_not_to_be_run

[Service]
EnvironmentFile=-/etc/default/ssh
ExecStartPre=/usr/sbin/sshd -f """ + sshd_conf_server.implode + """ -t
ExecStart=/usr/sbin/sshd -f """ + sshd_conf_server.implode + """ -D $SSHD_OPTS
ExecReload=/usr/sbin/sshd -f """ + sshd_conf_server.implode + """ -t
ExecReload=/bin/kill -HUP $MAINPID
KillMode=process
Restart=on-failure
RestartPreventExitStatus=255
Type=notify
RuntimeDirectory=sshd-phabricator
RuntimeDirectoryMode=0755

[Install]
WantedBy=multi-user.target
Alias=""" + ssh_name + """.service
""")

    for (config <- configs) {
      progress.echo("phabricator " + quote(config.name) + " port " +  server_port)
      config.execute("config set diffusion.ssh-port " + Bash.string(server_port.toString))

      if (test_server) {
        progress.bash(
          """unset DISPLAY
          echo "{}" | ssh -p """ + Bash.string(server_port.toString) +
          " -o StrictHostKeyChecking=false " +
          Bash.string(config.name) + """@localhost conduit conduit.ping""").print
      }
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool4 =
    Isabelle_Tool("phabricator_setup_ssh",
      "setup ssh service for all Phabricator installations", args =>
    {
      var server_port = default_server_port
      var system_port = default_system_port
      var test_server = false

      val getopts =
        Getopts("""
Usage: isabelle phabricator_setup_ssh [OPTIONS]

  Options are:
    -p PORT      sshd port for Phabricator servers (default: """ + default_server_port + """)
    -q PORT      sshd port for the operating system (default: """ + default_system_port + """)
    -T           test the ssh service for each Phabricator installation

  Configure ssh service for all Phabricator installations: a separate sshd
  is run in addition to the one of the operating system, and ports need to
  be distinct.

  A particular Phabricator installation is addressed by using its
  name as the ssh user; the actual Phabricator user is determined via
  stored ssh keys.
""",
          "p:" -> (arg => server_port = Value.Int.parse(arg)),
          "q:" -> (arg => system_port = Value.Int.parse(arg)),
          "T" -> (_ => test_server = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress

      phabricator_setup_ssh(
        server_port = server_port, system_port = system_port, test_server = test_server,
        progress = progress)
    })
}
