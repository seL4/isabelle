/*  Title:      Pure/Admin/components.scala
    Author:     Makarius

Isabelle system components.
*/

package isabelle


import java.io.{File => JFile}


object Components
{
  /* archive name */

  object Archive
  {
    val suffix: String = ".tar.gz"

    def apply(name: String): String =
      if (name == "") error("Bad component name: " + quote(name))
      else name + suffix

    def unapply(archive: String): Option[String] =
    {
      for {
        name0 <- Library.try_unsuffix(suffix, archive)
        name <- proper_string(name0)
      } yield name
    }

    def get_name(archive: String): String =
      unapply(archive) getOrElse
        error("Bad component archive name (expecting .tar.gz): " + quote(archive))
  }


  /* component collections */

  val default_components_base: Path = Path.explode("$ISABELLE_COMPONENTS_BASE")

  def admin(dir: Path): Path = dir + Path.explode("Admin/components")

  def contrib(dir: Path = Path.current, name: String = ""): Path =
    dir + Path.explode("contrib") + Path.explode(name)

  def unpack(dir: Path, archive: Path, progress: Progress = new Progress): String =
  {
    val name = Archive.get_name(archive.file_name)
    progress.echo("Unpacking " + name)
    Isabelle_System.gnutar("-xzf " + File.bash_path(archive), dir = dir).check
    name
  }

  def resolve(base_dir: Path, names: List[String],
    target_dir: Option[Path] = None,
    copy_dir: Option[Path] = None,
    progress: Progress = new Progress)
  {
    Isabelle_System.make_directory(base_dir)
    for (name <- names) {
      val archive_name = Archive(name)
      val archive = base_dir + Path.explode(archive_name)
      if (!archive.is_file) {
        val remote = Isabelle_System.getenv("ISABELLE_COMPONENT_REPOSITORY") + "/" + archive_name
        progress.echo("Getting " + remote)
        Bytes.write(archive, Url.read_bytes(Url(remote)))
      }
      for (dir <- copy_dir) {
        Isabelle_System.make_directory(dir)
        File.copy(archive, dir)
      }
      unpack(target_dir getOrElse base_dir, archive, progress = progress)
    }
  }

  def purge(dir: Path, platform: Platform.Family.Value)
  {
    def purge_platforms(platforms: String*): Set[String] =
      platforms.flatMap(name =>
        List("arm64-" + name, "x86-" + name, "x86_64_32-" + name, "x86_64-" + name)).toSet +
      "ppc-darwin" + "arm64-linux"
    val purge_set =
      platform match {
        case Platform.Family.linux => purge_platforms("darwin", "cygwin", "windows")
        case Platform.Family.macos => purge_platforms("linux", "cygwin", "windows")
        case Platform.Family.windows => purge_platforms("linux", "darwin")
      }

    File.find_files(dir.file,
      (file: JFile) => file.isDirectory && purge_set(file.getName),
      include_dirs = true).foreach(Isabelle_System.rm_tree)
  }


  /* component directory content */

  def settings(dir: Path = Path.current): Path = dir + Path.explode("etc/settings")
  def components(dir: Path = Path.current): Path = dir + Path.explode("etc/components")

  def check_dir(dir: Path): Boolean =
    settings(dir).is_file || components(dir).is_file

  def read_components(dir: Path): List[String] =
    split_lines(File.read(components(dir))).filter(_.nonEmpty)

  def write_components(dir: Path, lines: List[String]): Unit =
    File.write(components(dir), terminate_lines(lines))


  /* component repository content */

  val components_sha1: Path = Path.explode("~~/Admin/components/components.sha1")

  sealed case class SHA1_Digest(sha1: String, file_name: String)
  {
    override def toString: String = sha1 + "  " + file_name
  }

  def read_components_sha1(lines: List[String] = Nil): List[SHA1_Digest] =
    (proper_list(lines) getOrElse split_lines(File.read(components_sha1))).flatMap(line =>
      Word.explode(line) match {
        case Nil => None
        case List(sha1, name) => Some(SHA1_Digest(sha1, name))
        case _ => error("Bad components.sha1 entry: " + quote(line))
      })

  def write_components_sha1(entries: List[SHA1_Digest]): Unit =
    File.write(components_sha1, entries.sortBy(_.file_name).mkString("", "\n", "\n"))



  /** build and publish components **/

  def build_components(
    options: Options,
    components: List[Path],
    progress: Progress = new Progress,
    publish: Boolean = false,
    force: Boolean = false,
    update_components_sha1: Boolean = false)
  {
    val archives: List[Path] =
      for (path <- components) yield {
        path.file_name match {
          case Archive(_) => path
          case name =>
            if (!path.is_dir) error("Bad component directory: " + path)
            else if (!check_dir(path)) {
              error("Malformed component directory: " + path +
                "\n  (requires " + settings() + " or " + Components.components() + ")")
            }
            else {
              val component_path = path.expand
              val archive_dir = component_path.dir
              val archive_name = Archive(name)

              val archive = archive_dir + Path.explode(archive_name)
              if (archive.is_file && !force) {
                error("Component archive already exists: " + archive)
              }

              progress.echo("Packaging " + archive_name)
              Isabelle_System.gnutar("-czf " + File.bash_path(archive) + " " + Bash.string(name),
                dir = archive_dir).check

              archive
            }
        }
      }

    if ((publish && archives.nonEmpty) || update_components_sha1) {
      options.string("isabelle_components_server") match {
        case SSH.Target(user, host) =>
          using(SSH.open_session(options, host = host, user = user))(ssh =>
          {
            val components_dir = Path.explode(options.string("isabelle_components_dir"))
            val contrib_dir = Path.explode(options.string("isabelle_components_contrib_dir"))

            for (dir <- List(components_dir, contrib_dir) if !ssh.is_dir(dir)) {
              error("Bad remote directory: " + dir)
            }

            if (publish) {
              for (archive <- archives) {
                val archive_name = archive.file_name
                val name = Archive.get_name(archive_name)
                val remote_component = components_dir + archive.base
                val remote_contrib = contrib_dir + Path.explode(name)

                // component archive
                if (ssh.is_file(remote_component) && !force) {
                  error("Remote component archive already exists: " + remote_component)
                }
                progress.echo("Uploading " + archive_name)
                ssh.write_file(remote_component, archive)

                // contrib directory
                val is_standard_component =
                  Isabelle_System.with_tmp_dir("component")(tmp_dir =>
                  {
                    Isabelle_System.gnutar("-xzf " + File.bash_path(archive), dir = tmp_dir).check
                    check_dir(tmp_dir + Path.explode(name))
                  })
                if (is_standard_component) {
                  if (ssh.is_dir(remote_contrib)) {
                    if (force) ssh.rm_tree(remote_contrib)
                    else error("Remote component directory already exists: " + remote_contrib)
                  }
                  progress.echo("Unpacking remote " + archive_name)
                  ssh.execute("tar -C " + ssh.bash_path(contrib_dir) + " -xzf " +
                    ssh.bash_path(remote_component)).check
                }
                else {
                  progress.echo_warning("No unpacking of non-standard component: " + archive_name)
                }
              }
            }

            // remote SHA1 digests
            if (update_components_sha1) {
              val lines =
                for {
                  entry <- ssh.read_dir(components_dir)
                  if entry.is_file && entry.name.endsWith(Archive.suffix)
                }
                yield {
                  progress.echo("Digesting remote " + entry.name)
                  Library.trim_line(
                    ssh.execute("cd " + ssh.bash_path(components_dir) +
                      "; sha1sum " + Bash.string(entry.name)).check.out)
                }
              write_components_sha1(read_components_sha1(lines))
            }
          })
        case s => error("Bad isabelle_components_server: " + quote(s))
      }
    }

    // local SHA1 digests
    {
      val new_entries =
        for (archive <- archives)
        yield {
          val file_name = archive.file_name
          progress.echo("Digesting local " + file_name)
          val sha1 = SHA1.digest(archive).rep
          SHA1_Digest(sha1, file_name)
        }
      val new_names = new_entries.map(_.file_name).toSet

      write_components_sha1(
        new_entries :::
        read_components_sha1().filterNot(entry => new_names.contains(entry.file_name)))
    }
  }


  /* Isabelle tool wrapper */

  private val relevant_options =
    List("isabelle_components_server", "isabelle_components_dir", "isabelle_components_contrib_dir")

  val isabelle_tool =
    Isabelle_Tool("build_components", "build and publish Isabelle components",
      Scala_Project.here, args =>
    {
      var publish = false
      var update_components_sha1 = false
      var force = false
      var options = Options.init()

      def show_options: String =
        cat_lines(relevant_options.map(name => options.options(name).print))

      val getopts = Getopts("""
Usage: isabelle build_components [OPTIONS] ARCHIVES... DIRS...

  Options are:
    -P           publish on SSH server (see options below)
    -f           force: overwrite existing component archives and directories
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -u           update all SHA1 keys in Isabelle repository Admin/components

  Build and publish Isabelle components as .tar.gz archives on SSH server,
  depending on system options:

""" + Library.prefix_lines("  ", show_options) + "\n",
        "P" -> (_ => publish = true),
        "f" -> (_ => force = true),
        "o:" -> (arg => options = options + arg),
        "u" -> (_ => update_components_sha1 = true))

      val more_args = getopts(args)
      if (more_args.isEmpty && !update_components_sha1) getopts.usage()

      val progress = new Console_Progress

      build_components(options, more_args.map(Path.explode), progress = progress,
        publish = publish, force = force, update_components_sha1 = update_components_sha1)
    })
}
