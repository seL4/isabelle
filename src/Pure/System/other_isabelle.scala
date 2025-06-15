/*  Title:      Pure/System/other_isabelle.scala
    Author:     Makarius

Manage other Isabelle distributions: support historic versions starting from
tag "build_history_base".
*/

package isabelle


object Other_Isabelle {
  def apply(
    root: Path,
    isabelle_identifier: String = "",
    ssh: SSH.System = SSH.Local,
    progress: Progress = new Progress
  ): Other_Isabelle = {
    val (isabelle_home, url_prefix) =
      ssh match {
        case session: SSH.Session => (ssh.absolute_path(root), session.rsync_prefix)
        case _ =>
          if (proper_string(System.getenv("ISABELLE_SETTINGS_PRESENT")).isDefined) {
            error("Cannot manage other Isabelle distribution: global ISABELLE_SETTINGS_PRESENT")
          }
          (root.canonical, "")
      }
    val isabelle_home_url = url_prefix + isabelle_home.implode
    new Other_Isabelle(isabelle_home, isabelle_identifier, isabelle_home_url, ssh, progress)
  }
}

final class Other_Isabelle private(
  val isabelle_home: Path,
  val isabelle_identifier: String,
  isabelle_home_url: String,
  val ssh: SSH.System,
  val progress: Progress
) {
  other_isabelle =>

  override def toString: String = isabelle_home_url


  /* static system */

  def bash_context(script: String, cwd: Path = isabelle_home): String =
    Bash.context(script,
      user_home = ssh.user_home,
      isabelle_identifier = isabelle_identifier,
      cwd = cwd)

  def bash(
    script: String,
    cwd: Path = isabelle_home,
    input: String = "",
    redirect: Boolean = false,
    echo: Boolean = false,
    strict: Boolean = true
  ): Process_Result = {
    ssh.bash(bash_context(script, cwd = cwd),
      progress_stdout = progress.echo_if(echo, _),
      progress_stderr = progress.echo_if(echo, _),
      input = input,
      redirect = redirect,
      settings = false,
      strict = strict)
  }

  def getenv(name: String): String =
    ssh.execute(bash_context("bin/isabelle getenv -b " + Bash.string(name)),
      settings = false).check.out

  def getenv_strict(name: String): String =
    proper_string(getenv(name)) getOrElse
      error("Undefined Isabelle environment variable: " + quote(name) +
        "\nISABELLE_HOME=" + isabelle_home)

  val settings: Isabelle_System.Settings = (name: String) => getenv(name)

  def expand_path(path: Path): Path = path.expand_env(settings)
  def bash_path(path: Path): String = Bash.string(expand_path(path).implode)

  val isabelle_home_user: Path = expand_path(Path.explode("$ISABELLE_HOME_USER"))

  def host_db: Path = isabelle_home_user + Path.explode("host.db")

  def etc: Path = isabelle_home_user + Path.explode("etc")
  def etc_settings: Path = etc + Path.explode("settings")
  def etc_preferences: Path = etc + Path.explode("preferences")


  /* ML system settings */

  val ml_settings: ML_Settings =
    new ML_Settings {
      override def ml_system: String = getenv_strict("ML_SYSTEM")

      override def ml_platform: String =
        if ((isabelle_home + Path.explode("lib/Tools/console")).is_file) {
          val Pattern = """.*val ML_PLATFORM = "(.*)".*""".r
          val input = """val ML_PLATFORM = Option.getOpt (OS.Process.getEnv "ML_PLATFORM", "")"""
          val result = bash("bin/isabelle console -r", input = input)
          result.out match {
            case Pattern(a) if result.ok => a
            case _ =>
              error("Cannot get ML_PLATFORM from other Isabelle: " + isabelle_home +
                if_proper(result.err, "\n" + result.err))
          }
        }
        else getenv("ML_PLATFORM")
    }

  def user_output_dir: Path =
    isabelle_home_user + Path.basic("heaps") + Path.basic(ml_settings.ml_identifier)


  /* components */

  def init_components(
    components_base: String = Components.dynamic_components_base,
    catalogs: List[String] = Components.default_catalogs,
    components: List[String] = Nil
  ): List[String] = {
    val admin = Components.admin(Path.ISABELLE_HOME).implode

    catalogs.map(name =>
      "init_components " + quote(components_base) + " " + quote(admin + "/" + name)) :::
    components.map(name =>
      "init_component " + quote(components_base) + "/" + name)
  }

  def resolve_components(
    echo: Boolean = false,
    clean_platforms: Option[List[Platform.Family]] = None,
    clean_archives: Boolean = false,
    component_repository: String = Components.static_component_repository
  ): Unit = {
    val missing = Path.split(getenv("ISABELLE_COMPONENTS_MISSING"))
    for (path <- missing) {
      Components.resolve(path.dir, path.file_name,
        clean_platforms = clean_platforms,
        clean_archives = clean_archives,
        component_repository = component_repository,
        ssh = ssh,
        progress = if (echo) progress else new Progress)
    }
  }

  def scala_build(fresh: Boolean = false, echo: Boolean = false): Unit = {
    if (fresh) ssh.rm_tree(isabelle_home + Path.explode("lib/classes"))

    val dummy_stty = Path.explode("~~/lib/dummy_stty/stty")
    val dummy_stty_remote = expand_path(dummy_stty)
    if (!ssh.is_file(dummy_stty_remote)) {
      ssh.make_directory(dummy_stty_remote.dir)
      ssh.write_file(dummy_stty_remote, dummy_stty)
      ssh.set_executable(dummy_stty_remote)
    }
    try {
      bash(
        "export PATH=\"" + bash_path(dummy_stty_remote.dir) + ":$PATH\"\n" +
        "export CLASSPATH=" + Bash.string(getenv("ISABELLE_CLASSPATH")) + "\n" +
        "bin/isabelle jedit -b", echo = echo).check
    }
    catch { case ERROR(msg) => cat_error("Failed to build Isabelle/Scala/Java modules:", msg) }
  }


  /* settings */

  def clean_settings(): Boolean =
    if (!ssh.is_file(etc_settings)) true
    else if (ssh.read(etc_settings).startsWith("# generated by Isabelle")) {
      ssh.delete(etc_settings)
      true
    }
    else false

  def init_settings(settings: List[String]): Unit = {
    if (clean_settings()) {
      ssh.make_directory(etc_settings.dir)
      ssh.write(etc_settings,
        "# generated by Isabelle " + Date.now() + "\n" +
        "#-*- shell-script -*- :mode=shellscript:\n" +
        settings.mkString("\n", "\n", "\n"))
    }
    else error("Cannot proceed with existing user settings file: " + etc_settings)
  }

  def debug_settings(): List[String] = {
    val debug = System.getProperty("isabelle.debug", "") == "true"
    if (debug) {
      List("ISABELLE_JAVA_SYSTEM_OPTIONS=\"$ISABELLE_JAVA_SYSTEM_OPTIONS -Disabelle.debug=true\"")
    }
    else Nil
  }


  /* init */

  def init(
    other_settings: List[String] = init_components(),
    fresh: Boolean = false,
    echo: Boolean = false,
    clean_platforms: Option[List[Platform.Family]] = None,
    clean_archives: Boolean = false,
    component_repository: String = Components.static_component_repository
  ): Unit = {
    init_settings(other_settings)
    resolve_components(
      echo = echo,
      clean_platforms = clean_platforms,
      clean_archives = clean_archives,
      component_repository = component_repository)
    scala_build(fresh = fresh, echo = echo)
    Setup_Tool.init(other_isabelle)
  }


  /* cleanup */

  def cleanup(): Unit =
    ssh.delete(host_db, etc_settings, etc_preferences, etc, isabelle_home_user)
}
