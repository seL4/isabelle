/*  Title:      Pure/Tools/phabricator.scala
    Author:     Makarius

Support for Phabricator server. See also:
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

  val daemon_user = "phabricator"

  val ssh_standard = 22
  val ssh_alternative1 = 222
  val ssh_alternative2 = 2222


  /* installation parameters */

  val default_name = "vcs"

  def phabricator_name(name: String = "", ext: String = ""): String =
    "phabricator" + (if (name.isEmpty) "" else "-" + name) + (if (ext.isEmpty) "" else "." + ext)

  def isabelle_phabricator_name(name: String = "", ext: String = ""): String =
    "isabelle-" + phabricator_name(name = name, ext = ext)

  def default_root(options: Options, name: String): Path =
    Path.explode(options.string("phabricator_www_root")) +
    Path.basic(phabricator_name(name = name))

  def default_repo(options: Options, name: String): Path =
    default_root(options, name) + Path.basic("repo")



  /** global configuration **/

  val global_config = Path.explode("/etc/" + isabelle_phabricator_name(ext = "conf"))

  sealed case class Config(name: String, root: Path)
  {
    def home: Path = root + Path.explode(phabricator_name())

    def execute(command: String): Process_Result =
      Isabelle_System.bash("./bin/" + command, cwd = home.file).check
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
    options: Options,
    name: String = default_name,
    root: String = "",
    repo: String = "",
    package_update: Boolean = false,
    progress: Progress = No_Progress)
  {
    /* system environment */

    Linux.check_system_root()

    if (package_update) {
      Linux.package_update(progress = progress)
      Linux.check_reboot_required()
    }

    Linux.package_install(packages, progress = progress)
    Linux.check_reboot_required()


    /* users */

    if (name == daemon_user) {
      error("Clash of installation name with daemon user " + quote(daemon_user))
    }

    user_setup(daemon_user, "Phabricator Daemon User", ssh_setup = true)
    user_setup(name, "Phabricator SSH User")

    val www_user = options.string("phabricator_www_user")


    /* basic installation */

    val root_path = if (root.nonEmpty) Path.explode(root) else default_root(options, name)
    val repo_path = if (repo.nonEmpty) Path.explode(repo) else default_repo(options, name)

    val configs = read_config()

    for (config <- configs if config.name == name) {
      error("Duplicate Phabricator installation " + quote(name) + " in " + config.root)
    }

    if (!Isabelle_System.bash("mkdir -p " + File.bash_path(root_path)).ok) {
      error("Failed to create root directory " + root_path)
    }

    progress.bash(cwd = root_path.file, echo = true,
      script = """
        set -e
        chown """ + Bash.string(www_user) + ":" + Bash.string(www_user) + """ .
        chmod 755 .

        git clone https://github.com/phacility/libphutil.git
        git clone https://github.com/phacility/arcanist.git
        git clone https://github.com/phacility/phabricator.git
      """).check

    val config = Config(name, root_path)
    write_config(configs ::: List(config))

    config.execute("config set pygments.enabled true")


    /* local repository directory */

    if (!Isabelle_System.bash("mkdir -p " + File.bash_path(repo_path)).ok) {
      error("Failed to create local repository directory " + repo_path)
    }

    Isabelle_System.bash(cwd = repo_path.file,
      script = """
        set -e
        chown -R """ + Bash.string(daemon_user) + ":" + Bash.string(daemon_user) + """ .
        chmod 755 .
      """).check

    config.execute("config set repository.default-local-path " + File.bash_path(repo_path))


    /* MySQL setup */

    progress.echo("MySQL setup...")

    File.write(Path.explode("/etc/mysql/mysql.conf.d/" + phabricator_name(ext = "cnf")),
"""[mysqld]
max_allowed_packet = 32M
innodb_buffer_pool_size = 1600M
local_infile = 0
""")

    Linux.service_restart("mysql")


    def mysql_conf(R: Regex): Option[String] =
      split_lines(File.read(Path.explode(options.string("phabricator_mysql_config")))).
        collectFirst({ case R(a) => a })

    for (user <- mysql_conf("""^user\s*=\s*(\S*)\s*$""".r)) {
      config.execute("config set mysql.user " + Bash.string(user))
    }

    for (pass <- mysql_conf("""^password\s*=\s*(\S*)\s*$""".r)) {
      config.execute("config set mysql.pass " + Bash.string(pass))
    }

    config.execute("config set storage.default-namespace " +
      Bash.string(phabricator_name(name = name).replace("-", "_")))

    config.execute("config set storage.mysql-engine.max-size 8388608")

    config.execute("storage upgrade --force")


    /* SSH hosting */

    progress.echo("SSH hosting setup...")

    val ssh_port = ssh_alternative2

    config.execute("config set diffusion.ssh-user " + Bash.string(name))
    config.execute("config set diffusion.ssh-port " + ssh_port)

    val sudoers_file = Path.explode("/etc/sudoers.d") + Path.basic(isabelle_phabricator_name())
    File.write(sudoers_file,
      www_user + " ALL=(" + daemon_user + ") SETENV: NOPASSWD: /usr/bin/git, /usr/bin/hg, /usr/bin/ssh, /usr/bin/id\n" +
      name + " ALL=(" + daemon_user + ") SETENV: NOPASSWD: /usr/bin/git, /usr/bin/git-upload-pack, /usr/bin/git-receive-pack, /usr/bin/hg, /usr/bin/svnserve, /usr/bin/ssh, /usr/bin/id\n")

    Isabelle_System.bash("chmod 0440 " + File.bash_path(sudoers_file)).check


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

    progress.echo("Apache setup...")

    val apache_root = Path.explode(options.string("phabricator_apache_root"))
    val apache_sites = apache_root + Path.explode("sites-available")

    if (!apache_sites.is_dir) error("Bad Apache sites directory " + apache_sites)

    val server_name = phabricator_name(ext = "lvh.me")  // alias for "localhost" for testing
    val server_url = "http://" + server_name

    File.write(apache_sites + Path.basic(isabelle_phabricator_name(ext = "conf")),
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
      a2ensite """ + Bash.string(isabelle_phabricator_name())).check

    Linux.service_restart("apache2")


    /* PHP daemon */

    progress.echo("PHP daemon setup...")

    config.execute("config set phd.user " + Bash.string(daemon_user))

    Linux.service_install(isabelle_phabricator_name(),
"""[Unit]
Description=PHP daemon for Isabelle/Phabricator """ + quote(name) + """
After=syslog.target network.target apache2.service mysql.service

[Service]
Type=oneshot
User=""" + daemon_user + """
Group=""" + daemon_user + """
Environment=PATH=/sbin:/usr/sbin:/usr/local/sbin:/usr/local/bin:/usr/bin:/bin
ExecStart=""" + config.home.implode + """/bin/phd start
ExecStop=""" + config.home.implode + """/bin/phd stop
RemainAfterExit=yes

[Install]
WantedBy=multi-user.target
""")


    progress.echo("\nDONE\nWeb configuration via " + server_url)
  }


  /* Isabelle tool wrapper */

  val isabelle_tool1 =
    Isabelle_Tool("phabricator_setup", "setup Phabricator server on Ubuntu Linux", args =>
    {
      var repo = ""
      var package_update = false
      var options = Options.init()
      var root = ""

      val getopts =
        Getopts("""
Usage: isabelle phabricator_setup [OPTIONS] [NAME]

  Options are:
    -R DIR       repository directory (default: """ + default_repo(options, "NAME") + """)
    -U           full update of system packages before installation
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -r DIR       installation root directory (default: """ + default_root(options, "NAME") + """)

  Install Phabricator as Ubuntu LAMP application (Linux, Apache, MySQL, PHP).

  Slogan: "Discuss. Plan. Code. Review. Test.
  Every application your project needs, all in one tool."

  The installation NAME (default: """ + quote(default_name) + """) is mapped to
  a regular Unix user and used for public SSH access.
""",
          "R:" -> (arg => repo = arg),
          "U" -> (_ => package_update = true),
          "o:" -> (arg => options = options + arg),
          "r:" -> (arg => root = arg))

      val more_args = getopts(args)

      val name =
        more_args match {
          case Nil => default_name
          case List(name) => name
          case _ => getopts.usage()
        }

      val progress = new Console_Progress

      phabricator_setup(options, name, root = root, repo = repo,
        package_update = package_update, progress = progress)
    })



  /** update **/

  def phabricator_update(name: String, progress: Progress = No_Progress)
  {
    Linux.check_system_root()

    ???
  }


  /* Isabelle tool wrapper */

  val isabelle_tool2 =
    Isabelle_Tool("phabricator_update", "update Phabricator server installation", args =>
    {
      val getopts =
        Getopts("""
Usage: isabelle phabricator_update [NAME]

  Update Phabricator installation, with lookup of NAME (default + """ + quote(default_name) + """)
  in """ + global_config + "\n")

      val more_args = getopts(args)
      val name =
        more_args match {
          case Nil => default_name
          case List(name) => name
          case _ => getopts.usage()
        }

      val progress = new Console_Progress

      phabricator_update(name, progress = progress)
    })
}
