/*  Title:      Pure/System/components.scala
    Author:     Makarius

Isabelle system components.
*/

package isabelle


import java.io.{File => JFile}

import scala.jdk.CollectionConverters._


object Components {
  /* archive name */

  object Archive {
    val suffix: String = ".tar.gz"

    def apply(name: String): String =
      if (name == "") error("Bad component name: " + quote(name))
      else name + suffix

    def unapply(archive: String): Option[String] = {
      for {
        name0 <- Library.try_unsuffix(suffix, archive)
        name <- proper_string(name0)
      } yield name
    }

    def get_name(archive: String): String =
      unapply(archive) getOrElse
        error("Bad component archive name (expecting .tar.gz): " + quote(archive))
  }


  /* platforms */

  sealed case class Platforms(family_platforms: Map[String, List[Path]]) {
    def + (entry: (String, List[Path])): Platforms = Platforms(family_platforms + entry)
    def defined(family: String): Boolean = family_platforms.isDefinedAt(family)
    def apply(family: String): List[Path] = family_platforms.getOrElse(family, Nil)
    def path_iterator: Iterator[Path] = family_platforms.valuesIterator.flatten
  }

  val default_platforms: Platforms = {
    def paths(args: String*): List[Path] = args.toList.map(Path.explode)
    Platforms(
      Map(
        Platform.Family.linux_arm.toString ->
          paths("arm64-linux", "arm64_32-linux"),
        Platform.Family.linux.toString ->
          paths("x86_64-linux", "x86_64_32-linux"),
        Platform.Family.macos.toString ->
          paths("arm64-darwin", "arm64_32-darwin", "x86_64-darwin", "x86_64_32-darwin"),
        Platform.Family.windows.toString ->
          paths("x86_64-cygwin", "x86_64-windows", "x86_64_32-windows", "x86-windows"),
        "obsolete" -> paths("x86-linux", "x86-cygwin")
      ))
  }


  /* component collections */

  def static_component_repository: String =
    Isabelle_System.getenv("ISABELLE_COMPONENT_REPOSITORY")

  val default_components_base: Path = Path.explode("$ISABELLE_COMPONENTS_BASE")
  val dynamic_components_base: String = "${ISABELLE_COMPONENTS_BASE:-$USER_HOME/.isabelle/contrib}"
  val classic_components_base: Path = Path.explode("$USER_HOME/.isabelle/contrib")

  val default_catalogs: List[String] = List("main")
  val optional_catalogs: List[String] = List("main", "optional")

  def admin(dir: Path): Path = dir + Path.explode("Admin/components")

  def contrib(dir: Path = Path.current, name: String = ""): Path =
    dir + Path.explode("contrib") + Path.explode(name)

  def unpack(
    dir: Path,
    archive: Path,
    ssh: SSH.System = SSH.Local,
    progress: Progress = new Progress
  ): String = {
    val name = Archive.get_name(archive.file_name)
    progress.echo("Unpacking " + archive.base)
    ssh.execute(
      "tar -C " + ssh.bash_path(dir) + " -x -z -f " + ssh.bash_path(archive),
      progress_stdout = progress.echo(_),
      progress_stderr = progress.echo(_)).check
    name
  }

  def clean_base(
    base_dir: Path,
    platforms: List[Platform.Family] = Platform.Family.list,
    ssh: SSH.System = SSH.Local,
    progress: Progress = new Progress
  ): Unit = {
    for {
      name <- ssh.read_dir(base_dir)
      dir = base_dir + Path.basic(name)
      if is_component_dir(dir)
    } Directory(dir, ssh = ssh).clean(preserve = platforms, progress = progress)
  }

  def resolve(
    base_dir: Path,
    name: String,
    target_dir: Option[Path] = None,
    copy_dir: Option[Path] = None,
    clean_platforms: Option[List[Platform.Family]] = None,
    clean_archives: Boolean = false,
    component_repository: String = Components.static_component_repository,
    ssh: SSH.System = SSH.Local,
    progress: Progress = new Progress
  ): Unit = {
    ssh.make_directory(base_dir)

    val archive_name = Archive(name)
    val archive = base_dir + Path.basic(archive_name)
    if (!ssh.is_file(archive)) {
      val remote = Url.append_path(component_repository, archive_name)
      ssh.download_file(remote, archive, progress = progress)
    }

    for (dir <- copy_dir) {
      ssh.make_directory(dir)
      ssh.copy_file(archive, dir)
    }

    val unpack_dir = target_dir getOrElse base_dir
    unpack(unpack_dir, archive, ssh = ssh, progress = progress)

    if (clean_platforms.isDefined) {
      Directory(unpack_dir + Path.basic(name), ssh = ssh).
        clean(preserve = clean_platforms.get, progress = progress)
    }

    if (clean_archives) {
      progress.echo("Removing " + quote(archive_name))
      ssh.delete(archive)
    }
  }

  def provide(local_dir: Path,
    base_dir: Path = classic_components_base,
    ssh: SSH.System = SSH.Local,
    progress: Progress = new Progress
  ): Directory = {
    val base_name = local_dir.expand.base
    val local_directory = Directory(local_dir).check
    val remote_directory = Directory(base_dir + base_name, ssh = ssh)
    if (!remote_directory.ok) {
      progress.echo("Providing " + base_name + ssh.print)
      Isabelle_System.with_tmp_file("tmp", ext = "tar") { local_tmp_tar =>
        ssh.with_tmp_dir { remote_tmp_dir =>
          val remote_tmp_tar = remote_tmp_dir + Path.basic("tmp.tar")
          val remote_dir = ssh.make_directory(remote_directory.path)
          Isabelle_System.gnutar(
            "-cf " + File.bash_path(local_tmp_tar) + " .", dir = local_dir).check
          ssh.write_file(remote_tmp_tar, local_tmp_tar)
          ssh.execute(
            "tar -C " + ssh.bash_path(remote_dir) + " -xf " + ssh.bash_path(remote_tmp_tar)).check
        }
      }
    }
    remote_directory.check
  }


  /* component directories */

  def directories(): List[Path] =
    Path.split(Isabelle_System.getenv_strict("ISABELLE_COMPONENTS"))

  def is_component_dir(dir: Path, ssh: SSH.System = SSH.Local): Boolean =
    ssh.is_file(dir + Path.explode("etc/settings")) ||
    ssh.is_file(dir + Path.explode("etc/components"))


  /* component directory content */

  object Directory {
    def apply(path: Path, ssh: SSH.System = SSH.Local): Directory =
      new Directory(ssh.absolute_path(path), ssh)
  }

  class Directory private(val path: Path, val ssh: SSH.System = SSH.Local) {
    override def toString: String = path.toString + ssh.print

    def etc: Path = path + Path.basic("etc")
    def src: Path = path + Path.basic("src")
    def bin: Path = path + Path.basic("bin")
    def lib: Path = path + Path.basic("lib")
    def settings: Path = etc + Path.basic("settings")
    def components: Path = etc + Path.basic("components")
    def build_props: Path = etc + Path.basic("build.props")
    def platform_props: Path = etc + Path.basic("platform.props")
    def README: Path = path + Path.basic("README")
    def LICENSE: Path = path + Path.basic("LICENSE")

    def create(progress: Progress = new Progress, permissive: Boolean = false): Directory = {
      if (!permissive || !ssh.is_dir(path)) {
        progress.echo("Creating component directory " + toString)
        ssh.new_directory(path)
      }
      ssh.make_directory(etc)
      this
    }

    def write_platforms(
      lines: List[String] = Platform.Family.list.map(family => family.toString + " = ")
    ): Directory = {
      File.write(platform_props, terminate_lines(lines))
      this
    }

    def get_platforms(): Platforms = {
      val props_path = platform_props.expand
      val props =
        if (props_path.is_file) {
          try {
            for (case (a, b) <- File.read_props(props_path).asScala.toList)
              yield {
                if (!default_platforms.defined(a)) error("Bad platform family " + quote(a))
                val ps = List.from(b.split("\\s+").iterator.filter(_.nonEmpty)).map(Path.explode)
                for (p <- ps if !p.all_basic) error("Bad path outside component " + p)
                a -> ps
              }
          }
          catch { case ERROR(msg) => error(msg + Position.here(Position.File(props_path.implode))) }
        }
        else Nil
      props.foldLeft(default_platforms)(_ + _)
    }

    def clean(
      preserve: List[Platform.Family] = Platform.Family.list,
      progress: Progress = new Progress
    ): Unit = {
      val platforms = get_platforms()
      val preserve_path = Set.from(for (a <- preserve; p <- platforms(a.toString)) yield p)
      for (dir <- platforms.path_iterator if !preserve_path(dir) && ssh.is_dir(path + dir)) {
        progress.echo("Removing " + (path.base + dir))
        ssh.rm_tree(path + dir)
      }
    }

    def ok: Boolean =
      ssh.is_file(settings) || ssh.is_file(components) || Sessions.is_session_dir(path, ssh = ssh)

    def check: Directory =
      if (!ssh.is_dir(path)) error("Bad component directory: " + toString)
      else if (!ok) {
        error("Malformed component directory: " + toString +
          "\n  (missing \"etc/settings\" or \"etc/components\" or \"ROOT\" or \"ROOTS\")")
      }
      else this

    def read_components(): List[String] =
      split_lines(ssh.read(components)).filter(_.nonEmpty)
    def write_components(lines: List[String]): Unit =
      ssh.write(components, terminate_lines(lines))

    def write_settings(text: String): Unit =
      ssh.write(settings, "# -*- shell-script -*- :mode=shellscript:\n" + text)
  }


  /* component repository content */

  val components_sha1: Path = Path.explode("~~/Admin/components/components.sha1")

  sealed case class SHA1_Entry(digest: SHA1.Digest, name: String) {
    override def toString: String = SHA1.shasum(digest, name).toString
  }

  def read_components_sha1(lines: List[String] = Nil): List[SHA1_Entry] =
    (proper_list(lines) getOrElse split_lines(File.read(components_sha1))).flatMap(line =>
      Word.explode(line) match {
        case Nil => None
        case List(sha1, name) => Some(SHA1_Entry(SHA1.fake_digest(sha1), name))
        case _ => error("Bad components.sha1 entry: " + quote(line))
      })

  def write_components_sha1(entries: List[SHA1_Entry]): Unit =
    File.write(components_sha1, entries.sortBy(_.name).mkString)


  /** manage user components **/

  val components_path: Path = Path.explode("$ISABELLE_HOME_USER/etc/components")

  def read_components(): List[String] =
    if (components_path.is_file) Library.trim_split_lines(File.read(components_path))
    else Nil

  def write_components(lines: List[String]): Unit = {
    Isabelle_System.make_directory(components_path.dir)
    File.write(components_path, terminate_lines(lines))
  }

  def update_components(add: Boolean, path0: Path, progress: Progress = new Progress): Unit = {
    val path = path0.expand.absolute
    if (add) Directory(path).check

    val lines1 = read_components()
    val lines2 =
      lines1.filter(line =>
        line.isEmpty || line.startsWith("#") || !File.eq(Path.explode(line), path))
    val lines3 = if (add) lines2 ::: List(path.implode) else lines2

    if (lines1 != lines3) write_components(lines3)

    val prefix = if (lines1 == lines3) "Unchanged" else if (add) "Added" else "Removed"
    progress.echo(prefix + " component " + path)
  }


  /* main entry point */

  def main(args: Array[String]): Unit = {
    Command_Line.tool {
      for (arg <- args) {
        val add =
          if (arg.startsWith("+")) true
          else if (arg.startsWith("-")) false
          else error("Bad argument: " + quote(arg))
        val path = Path.explode(arg.substring(1))
        update_components(add, path, progress = new Console_Progress)
      }
    }
  }


  /** build and publish components **/

  def components_build(
    options: Options,
    components: List[Path],
    progress: Progress = new Progress,
    publish: Boolean = false,
    force: Boolean = false,
    update_components_sha1: Boolean = false
  ): Unit = {
    val archives: List[Path] =
      for (path <- components) yield {
        path.file_name match {
          case Archive(_) => path
          case name =>
            Directory(path).check
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

    if ((publish && archives.nonEmpty) || update_components_sha1) {
      val server = options.string("isabelle_components_server")
      if (server.isEmpty) error("Undefined option isabelle_components_server")

      using(SSH.open_session(options, server)) { ssh =>
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
              Isabelle_System.with_tmp_dir("component") { tmp_dir =>
                Isabelle_System.extract(archive, tmp_dir)
                Directory(tmp_dir + Path.explode(name)).ok
              }
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
              if ssh.is_file(components_dir + Path.basic(entry)) &&
                entry.endsWith(Archive.suffix)
            }
            yield {
              progress.echo("Digesting remote " + entry)
              ssh.execute("cd " + ssh.bash_path(components_dir) +
                "; sha1sum " + Bash.string(entry)).check.out
            }
          write_components_sha1(read_components_sha1(lines))
        }
      }
    }

    // local SHA1 digests
    {
      val new_entries =
        for (archive <- archives)
        yield {
          val name = archive.file_name
          progress.echo("Digesting local " + name)
          SHA1_Entry(SHA1.digest(archive), name)
        }
      val new_names = new_entries.map(_.name).toSet

      write_components_sha1(
        new_entries :::
        read_components_sha1().filterNot(entry => new_names.contains(entry.name)))
    }
  }


  /* Isabelle tool wrapper */

  private val relevant_options =
    List("isabelle_components_server", "isabelle_components_dir", "isabelle_components_contrib_dir")

  val isabelle_tool =
    Isabelle_Tool("components_build", "build and publish Isabelle components",
      Scala_Project.here,
      { args =>
        var publish = false
        var update_components_sha1 = false
        var force = false
        var options = Options.init()

        def show_options: String =
          cat_lines(relevant_options.flatMap(options.get).map(_.print))

        val getopts = Getopts("""
Usage: isabelle components_build [OPTIONS] ARCHIVES... DIRS...

  Options are:
    -P           publish on SSH server (see options below)
    -f           force: overwrite existing component archives and directories
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -u           update all SHA1 keys in Isabelle repository Admin/components

  Build and publish Isabelle components as .tar.gz archives on SSH server,
  depending on system options:

""" + Library.indent_lines(2, show_options) + "\n",
          "P" -> (_ => publish = true),
          "f" -> (_ => force = true),
          "o:" -> (arg => options = options + arg),
          "u" -> (_ => update_components_sha1 = true))

        val more_args = getopts(args)
        if (more_args.isEmpty && !update_components_sha1) getopts.usage()

        val progress = new Console_Progress

        components_build(options, more_args.map(Path.explode), progress = progress,
          publish = publish, force = force, update_components_sha1 = update_components_sha1)
      })
}
