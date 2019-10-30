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

  val default_name = "vcs"

  def default_prefix(name: String): String = "phabricator-" + name

  def default_root(options: Options, name: String): Path =
    Path.explode(options.string("phabricator_www_root")) + Path.basic(default_prefix(name))

  def default_repo(options: Options, name: String): Path =
    default_root(options, name) + Path.basic("repo")

  val packages: List[String] =
    Build_Docker.packages :::
    // https://secure.phabricator.com/source/phabricator/browse/master/scripts/install/install_ubuntu.sh 15e6e2adea61
    List("git", "mysql-server", "apache2", "libapache2-mod-php", "php", "php-mysql",
      "php-gd", "php-curl", "php-apcu", "php-cli", "php-json", "php-mbstring")



  /** global configuration **/

  val global_config = Path.explode("/etc/isabelle-phabricator.conf")

  sealed case class Config(name: String, root: Path)
  {
    def home: Path = root + Path.explode("phabricator")

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

  def phabricator_setup(
    options: Options,
    name: String = default_name,
    prefix: String = "",
    root: String = "",
    repo: String = "",
    progress: Progress = No_Progress)
  {
    /* system environment */

    Linux.check_system_root()

    Linux.package_update(progress = progress)
    Linux.check_reboot_required()

    Linux.package_install(packages, progress = progress)
    Linux.check_reboot_required()


    /* basic installation */

    val prefix_name = proper_string(prefix) getOrElse default_prefix(name)
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
        chown """ + Bash.string(options.string("phabricator_www_user")) + """ .
        chmod 755 .

        git clone https://github.com/phacility/libphutil.git
        git clone https://github.com/phacility/arcanist.git
        git clone https://github.com/phacility/phabricator.git
      """).check

    val config = Config(name, root_path)
    write_config(configs ::: List(config))


    /* MySQL setup */

    progress.echo("MySQL setup...")

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
      Bash.string(prefix_name.replace("-", "_")))

    config.execute("storage upgrade --force")


    /* Apache setup */

    progress.echo("Apache setup...")

    val apache_root = Path.explode(options.string("phabricator_apache_root"))
    val apache_sites = apache_root + Path.explode("sites-available")

    if (!apache_sites.is_dir) error("Bad Apache sites directory " + apache_sites)

    File.write(apache_sites + Path.basic(prefix_name + ".conf"),
"""<VirtualHost *:80>
    #ServerName: "lvh.me" is an alias for "localhost" for testing
    ServerName """ + prefix_name + """.lvh.me
    ServerAdmin webmaster@localhost
    DocumentRoot """ + config.home.implode + """/webroot

    ErrorLog ${APACHE_LOG_DIR}/error.log
    RewriteEngine on
    RewriteRule ^(.*)$  /index.php?__path__=$1  [B,L,QSA]
</VirtualHost>

# vim: syntax=apache ts=4 sw=4 sts=4 sr noet
""")

    Isabelle_System.bash("""
      set -e
      a2enmod rewrite
      a2ensite """ + Bash.string(prefix_name) + """
      systemctl restart apache2
""").check

    progress.echo("\nDONE\nWeb configuration via http://" + prefix_name + ".lvh.me")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool1 =
    Isabelle_Tool("phabricator_setup", "setup Phabricator server on Ubuntu Linux", args =>
    {
      var options = Options.init()
      var prefix = ""
      var root = ""
      var repo = ""

      val getopts =
        Getopts("""
Usage: isabelle phabricator_setup [OPTIONS] [NAME]

  Options are:
    -R DIR       repository directory (default: """ + default_repo(options, "NAME") + """)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -p PREFIX    prefix for derived names (default: """ + default_prefix("NAME") + """)
    -r DIR       installation root directory (default: """ + default_root(options, "NAME") + """)

  Install Phabricator as Ubuntu LAMP application (Linux, Apache, MySQL, PHP).

  Slogan: "Discuss. Plan. Code. Review. Test.
  Every application your project needs, all in one tool."

  The installation NAME (default: """ + quote(default_name) + """) is mapped to
  a regular Unix user and used for public SSH access.
""",
          "R:" -> (arg => repo = arg),
          "o:" -> (arg => options = options + arg),
          "p:" -> (arg => prefix = arg),
          "r:" -> (arg => root = arg))

      val more_args = getopts(args)

      val name =
        more_args match {
          case Nil => default_name
          case List(name) => name
          case _ => getopts.usage()
        }

      val progress = new Console_Progress

      phabricator_setup(options, name, prefix = prefix, root = root, repo = repo,
        progress = progress)
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
