/*  Title:      Pure/System/isabelle_system.scala
    Author:     Makarius

Miscellaneous Isabelle system operations.
*/

package isabelle


import java.util.{Map => JMap, HashMap}
import java.util.zip.ZipFile
import java.io.{File => JFile, IOException}
import java.net.ServerSocket
import java.nio.file.{Path => JPath, Files, SimpleFileVisitor, FileVisitResult,
  StandardCopyOption, FileSystemException}
import java.nio.file.attribute.BasicFileAttributes

import scala.jdk.CollectionConverters._


object Isabelle_System {
  /* settings environment */

  trait Settings { def get(name: String): String }
  trait Settings_Env extends Settings { def env: JMap[String, String] }

  class Env(val env: JMap[String, String]) extends Settings_Env {
    override def get(name: String): String = Option(env.get(name)).getOrElse("")
  }

  object No_Env extends Env(JMap.of())

  object Settings {
    def env(putenv: List[(String, String)] = Nil): JMap[String, String] = {
      val env0 = isabelle.setup.Environment.settings()
      if (putenv.isEmpty) env0
      else {
        val env = new HashMap(env0)
        for ((a, b) <- putenv) env.put(a, b)
        env
      }
    }

    def apply(putenv: List[(String, String)] = Nil): Settings_Env =
      new Env(env(putenv = putenv))
  }

  def getenv(name: String, env: Settings = Settings()): String = env.get(name)

  def getenv_strict(name: String, env: Settings = Settings()): String =
    proper_string(getenv(name, env)) getOrElse
      error("Undefined Isabelle environment variable: " + quote(name))

  def hostname(default: String = ""): String =
    proper_string(default) getOrElse getenv_strict("ISABELLE_HOSTNAME")


  /* services */

  type Service = Classpath.Service

  @volatile private var _classpath: Option[Classpath] = None

  def classpath(): Classpath = {
    if (_classpath.isEmpty) init()  // unsynchronized check
    _classpath.get
  }

  def make_services[C](c: Class[C]): List[C] = classpath().make_services(c)


  /* init settings + classpath */

  def init(isabelle_root: String = "", cygwin_root: String = ""): Unit = {
    isabelle.setup.Environment.init(isabelle_root, cygwin_root)
    synchronized {
      if (_classpath.isEmpty) _classpath = Some(Classpath())
    }
    Registry.global
  }


  /* getetc -- static distribution parameters */

  def getetc(name: String, root: Path = Path.ISABELLE_HOME): Option[String] = {
    val path = root + Path.basic("etc") + Path.basic(name)
    if (path.is_file) {
      Library.trim_split_lines(File.read(path)) match {
        case Nil => None
        case List(s) => Some(s)
        case _ => error("Single line expected in " + path.absolute)
      }
    }
    else None
  }


  /* Isabelle distribution identification */

  def isabelle_id(root: Path = Path.ISABELLE_HOME): String =
    getetc("ISABELLE_ID", root = root) orElse
    Mercurial.archive_id(root) orElse
    Mercurial.id_repository(root, rev = "") orElse
    Mercurial.sync_id(root) getOrElse
    error("Failed to identify Isabelle distribution " + root.expand)

  object Isabelle_Id extends Scala.Fun_String("isabelle_id") {
    val here = Scala_Project.here
    def apply(arg: String): String = isabelle_id()
  }

  def isabelle_tags(root: Path = Path.ISABELLE_HOME): String =
    getetc("ISABELLE_TAGS", root = root) orElse Mercurial.archive_tags(root) getOrElse {
      if (Mercurial.is_repository(root)) {
        val hg = Mercurial.repository(root)
        hg.tags(rev = hg.parent())
      }
      else ""
    }

  def isabelle_identifier(): Option[String] = proper_string(getenv("ISABELLE_IDENTIFIER"))

  def isabelle_heading(): String =
    isabelle_identifier() match {
      case None => ""
      case Some(version) => " (" + version + ")"
    }

  def isabelle_name(): String = getenv_strict("ISABELLE_NAME")

  def identification(): String =
    "Isabelle" + (try { "/" + isabelle_id () } catch { case ERROR(_) => "" }) + isabelle_heading()


  /** file-system operations **/

  /* scala functions */

  private def apply_paths(
    args: List[String],
    fun: PartialFunction[List[Path], Unit]
  ): List[String] = {
    fun(args.map(Path.explode))
    Nil
  }

  private def apply_paths1(args: List[String], fun: Path => Unit): List[String] =
    apply_paths(args, { case List(path) => fun(path) })

  private def apply_paths2(args: List[String], fun: (Path, Path) => Unit): List[String] =
    apply_paths(args, { case List(path1, path2) => fun(path1, path2) })

  private def apply_paths3(args: List[String], fun: (Path, Path, Path) => Unit): List[String] =
    apply_paths(args, { case List(path1, path2, path3) => fun(path1, path2, path3) })


  /* permissions */

  def chmod(arg: String, path: Path): Unit =
    bash("chmod " + arg + " " + File.bash_path(path)).check

  def chown(arg: String, path: Path): Unit =
    bash("chown " + arg + " " + File.bash_path(path)).check


  /* directories */

  def make_directory(path: Path): Path = {
    if (!path.is_dir) {
      try { Files.createDirectories(path.java_path) }
      catch { case ERROR(_) => error("Failed to create directory: " + path.absolute) }
    }
    path
  }

  def new_directory(path: Path): Path =
    if (path.is_dir) error("Directory already exists: " + path.absolute)
    else make_directory(path)

  def copy_dir(dir1: Path, dir2: Path, direct: Boolean = false): Unit = {
    def make_path(dir: Path): String =
      Url.dir_path(File.standard_path(dir.absolute), direct = direct)
    val p1 = make_path(dir1)
    val p2 = make_path(dir2)
    make_directory(if (direct) dir2.absolute else dir2.absolute.dir)
    val res = bash("cp -a " + Bash.string(p1) + " " + Bash.string(p2))
    if (!res.ok) cat_error("Failed to copy " + quote(p1) + " to " + quote(p2), res.err)
  }

  def with_copy_dir[A](dir1: Path, dir2: Path)(body: => A): A = {
    new_directory(dir2)
    try { copy_dir(dir1, dir2, direct = true); body }
    finally { rm_tree(dir2) }
  }


  object Make_Directory extends Scala.Fun_Strings("make_directory") {
    val here = Scala_Project.here
    def apply(args: List[String]): List[String] = apply_paths1(args, make_directory)
  }

  object Copy_Dir extends Scala.Fun_Strings("copy_dir") {
    val here = Scala_Project.here
    def apply(args: List[String]): List[String] = apply_paths2(args, copy_dir(_, _))
  }


  /* copy files */

  def copy_file(src: JFile, dst: JFile): Unit = {
    val target = if (dst.isDirectory) new JFile(dst, src.getName) else dst
    if (!File.eq(src, target)) {
      try {
        Files.copy(src.toPath, target.toPath,
          StandardCopyOption.COPY_ATTRIBUTES,
          StandardCopyOption.REPLACE_EXISTING)
      }
      catch {
        case ERROR(msg) =>
          cat_error("Failed to copy file " +
            File.path(src).absolute + " to " + File.path(target).absolute, msg)
      }
    }
  }

  def copy_file(src: Path, dst: Path): Unit = copy_file(src.file, dst.file)

  def copy_file_base(base_dir: Path, src: Path, target_dir: Path): Unit = {
    val src1 = src.expand
    val src1_dir = src1.dir
    if (!src1.starts_basic) {
      error("Illegal path specification " + src1 + " beyond base directory " + base_dir.absolute)
    }
    copy_file(base_dir + src1, Isabelle_System.make_directory(target_dir + src1_dir))
  }


  object Copy_File extends Scala.Fun_Strings("copy_file") {
    val here = Scala_Project.here
    def apply(args: List[String]): List[String] = apply_paths2(args, copy_file)
  }

  object Copy_File_Base extends Scala.Fun_Strings("copy_file_base") {
    val here = Scala_Project.here
    def apply(args: List[String]): List[String] = apply_paths3(args, copy_file_base)
  }


  /* move files */

  def move_file(src: JFile, dst: JFile): Unit = {
    val target = if (dst.isDirectory) new JFile(dst, src.getName) else dst
    if (!File.eq(src, target))
      Files.move(src.toPath, target.toPath, StandardCopyOption.REPLACE_EXISTING)
  }

  def move_file(src: Path, dst: Path): Unit = move_file(src.file, dst.file)


  /* symbolic link */

  def symlink(src: Path, dst: Path, force: Boolean = false, native: Boolean = false): Unit = {
    val src_file = src.file
    val dst_file = dst.file
    val target = if (dst_file.isDirectory) new JFile(dst_file, src_file.getName) else dst_file

    if (force) target.delete

    def cygwin_link(): Unit = {
      if (native) {
        error("Failed to create native symlink on Windows: " + quote(src_file.toString) +
          "\n(but it could work as Administrator)")
      }
      else isabelle.setup.Environment.cygwin_link(File.standard_path(src), target)
    }


    try { Files.createSymbolicLink(target.toPath, src_file.toPath) }
    catch {
      case _: UnsupportedOperationException if Platform.is_windows => cygwin_link()
      case _: FileSystemException if Platform.is_windows => cygwin_link()
    }
  }


  /* tmp files */

  def isabelle_tmp_prefix(): JFile = {
    val path = Path.explode("$ISABELLE_TMP_PREFIX")
    path.file.mkdirs  // low-level mkdirs to avoid recursion via Isabelle environment
    File.platform_file(path)
  }

  def tmp_file(
    name: String,
    ext: String = "",
    base_dir: JFile = isabelle_tmp_prefix(),
    initialized: Boolean = true
  ): JFile = {
    val suffix = if_proper(ext, "." + ext)
    val file = Files.createTempFile(base_dir.toPath, name, suffix).toFile
    if (initialized) file.deleteOnExit() else file.delete()
    file
  }

  def with_tmp_file[A](
    name: String,
    ext: String = "",
    base_dir: JFile = isabelle_tmp_prefix()
  )(body: Path => A): A = {
    val file = tmp_file(name, ext, base_dir = base_dir)
    try { body(File.path(file)) } finally { file.delete }
  }


  /* tmp dirs */

  def rm_tree(root: JFile): Unit = {
    root.delete
    if (root.isDirectory) {
      Files.walkFileTree(root.toPath,
        new SimpleFileVisitor[JPath] {
          override def visitFile(file: JPath, attrs: BasicFileAttributes): FileVisitResult = {
            try { Files.deleteIfExists(file) }
            catch { case _: IOException => }
            FileVisitResult.CONTINUE
          }

          override def postVisitDirectory(dir: JPath, e: IOException): FileVisitResult = {
            if (e == null) {
              try { Files.deleteIfExists(dir) }
              catch { case _: IOException => }
              FileVisitResult.CONTINUE
            }
            else throw e
          }
        }
      )
    }
  }

  def rm_tree(root: Path): Unit = rm_tree(root.file)

  object Rm_Tree extends Scala.Fun_Strings("rm_tree") {
    val here = Scala_Project.here
    def apply(args: List[String]): List[String] = apply_paths1(args, rm_tree)
  }

  def tmp_dir(name: String, base_dir: JFile = isabelle_tmp_prefix()): JFile = {
    val dir = Files.createTempDirectory(base_dir.toPath, name).toFile
    dir.deleteOnExit()
    dir
  }

  def with_tmp_dir[A](
    name: String,
    base_dir: JFile = isabelle_tmp_prefix()
  )(body: Path => A): A = {
    val dir = tmp_dir(name, base_dir = base_dir)
    try { body(File.path(dir)) } finally { rm_tree(dir) }
  }


  /* quasi-atomic update of directory */

  def update_directory(dir: Path, f: Path => Unit): Unit = {
    val new_dir = dir.ext("new")
    val old_dir = dir.ext("old")

    rm_tree(new_dir)
    rm_tree(old_dir)

    f(new_dir)

    if (dir.is_dir) move_file(dir, old_dir)
    move_file(new_dir, dir)
    rm_tree(old_dir)
  }


  /* TCP/IP ports */

  def local_port(): Int = {
    val socket = new ServerSocket(0)
    val port = socket.getLocalPort
    socket.close()
    port
  }


  /* JVM shutdown hook */

  def create_shutdown_hook(body: => Unit): Thread = {
    val shutdown_hook = Isabelle_Thread.create(new Runnable { def run(): Unit = body })

    try { Runtime.getRuntime.addShutdownHook(shutdown_hook) }
    catch { case _: IllegalStateException => }

    shutdown_hook
  }

  def remove_shutdown_hook(shutdown_hook: Thread): Unit =
    try { Runtime.getRuntime.removeShutdownHook(shutdown_hook) }
    catch { case _: IllegalStateException => }



  /** external processes **/

  /* GNU bash */

  def bash(script: String,
    description: String = "",
    ssh: SSH.System = SSH.Local,
    cwd: Path = Path.current,
    env: JMap[String, String] = Settings.env(),  // ignored for remote ssh
    redirect: Boolean = false,
    input: String = "",
    progress_stdout: String => Unit = (_: String) => (),
    progress_stderr: String => Unit = (_: String) => (),
    watchdog: Bash.Watchdog = Bash.Watchdog.none,
    strict: Boolean = true,
    cleanup: () => Unit = () => ()
  ): Process_Result = {
    Bash.process(script, description = description, ssh = ssh, cwd = cwd, env = env,
        redirect = redirect, cleanup = cleanup).
      result(input = input, progress_stdout = progress_stdout, progress_stderr = progress_stderr,
        watchdog = watchdog, strict = strict)
  }


  /* command-line tools */

  def require_command(cmd: String, test: String = "--version"): Unit = {
    if (!bash(Bash.string(cmd) + " " + test).ok) error("Missing system command: " + quote(cmd))
  }

  private lazy val gnutar_check: Boolean =
    try { bash("tar --version").check.out.containsSlice("GNU tar") || error("") }
    catch { case ERROR(_) => false }

  def gnutar(
    args: String,
    dir: Path = Path.current,
    original_owner: Boolean = false,
    strip: Boolean = false,
    redirect: Boolean = false
  ): Process_Result = {
    val options =
      (if (dir.is_current) "" else "-C " + File.bash_path(dir) + " ") +
      (if (original_owner) "" else "--owner=root --group=staff ") +
      (if (!strip) "" else "--strip-components=1 ")

    if (gnutar_check) bash("tar " + options + args, redirect = redirect)
    else error("Expected to find GNU tar executable")
  }

  def extract(archive: Path, dir: Path, strip: Boolean = false): Unit = {
    val name = archive.file_name
    make_directory(dir)
    if (File.is_zip(name) || File.is_jar(name)) {
      using(new ZipFile(archive.file)) { zip_file =>
        val items =
          for (entry <- zip_file.entries().asScala.toList)
          yield {
            val input = JPath.of(entry.getName)
            val count = input.getNameCount
            val output =
              if (strip && count <= 1) None
              else if (strip) Some(input.subpath(1, count))
              else Some(input)
            val result = output.map(dir.java_path.resolve(_))
            for (res <- result) {
              if (entry.isDirectory) Files.createDirectories(res)
              else {
                val bytes = using(zip_file.getInputStream(entry))(Bytes.read_stream(_))
                Files.createDirectories(res.getParent)
                Files.write(res, bytes.make_array)
              }
            }
            (entry, result)
          }
        for {
          case (entry, Some(res)) <- items
          if !entry.isDirectory
          t <- Option(entry.getLastModifiedTime)
        } Files.setLastModifiedTime(res, t)
      }
    }
    else {
      val extr =
        if (File.is_tar_bz2(name)) "-xjf"
        else if (File.is_tgz(name) || File.is_tar_gz(name)) "-xzf"
        else if (File.is_tar_xz(name)) "--xz -xf"
        else ""
      if (extr.nonEmpty) {
        Isabelle_System.gnutar(extr + " " + File.bash_path(archive), dir = dir, strip = strip).check
      }
      else error("Cannot extract " + archive)
    }
  }

  def make_patch(base_dir: Path, src: Path, dst: Path, diff_options: String = ""): String = {
    val lines =
      Isabelle_System.bash(
        "diff -Nru" + if_proper(diff_options, " " + diff_options) + " -- " +
          File.bash_path(src) + " " + File.bash_path(dst),
        cwd = base_dir).check_rc(Process_Result.RC.regular).out_lines
    Library.terminate_lines(lines)
  }

  def git_clone(url: String, target: Path,
    checkout: String = "HEAD",
    ssh: SSH.System = SSH.Local,
    progress: Progress = new Progress
  ): Unit = {
    progress.echo("Cloning " + quote(url) + " ...")
    bash(
      "git clone --quiet --no-checkout " + Bash.string(url) + " . && " +
      "git checkout --quiet --detach " + Bash.string(checkout),
      ssh = ssh, cwd = ssh.make_directory(target)).check
  }

  def open(arg: String): Unit =
    bash("exec \"$ISABELLE_OPEN\" " + Bash.string(arg) + " >/dev/null 2>/dev/null &")

  def pdf_viewer(arg: Path): Unit =
    bash("exec \"$PDF_VIEWER\" " + File.bash_path(arg) + " >/dev/null 2>/dev/null &")

  def open_external_file(name: String): Boolean = {
    val ext = Library.take_suffix((c: Char) => c != '.', name.toList)._2.mkString
    val external =
      ext.nonEmpty && space_explode(':', getenv("ISABELLE_EXTERNAL_FILES")).contains(ext)
    if (external) {
      if (ext == "pdf" && Path.is_wellformed(name)) pdf_viewer(Path.explode(name))
      else open(name)
    }
    external
  }



  /** Isabelle resources **/

  /* repository clone with Admin */

  def admin(): Boolean = Path.explode("~~/Admin").is_dir


  /* default logic */

  def default_logic(args: String*): String = {
    args.find(_ != "") match {
      case Some(logic) => logic
      case None => getenv_strict("ISABELLE_LOGIC")
    }
  }


  /* download file */

  def download(url_name: String, progress: Progress = new Progress): HTTP.Content = {
    val url = Url(url_name)
    progress.echo("Getting " + quote(url_name))
    try { HTTP.Client.get(url) }
    catch { case ERROR(msg) => cat_error("Failed to download " + quote(url_name), msg) }
  }

  def download_file(url_name: String, file: Path, progress: Progress = new Progress): Unit =
    Bytes.write(file, download(url_name, progress = progress).bytes)

  object Download extends Scala.Fun("download", thread = true) {
    val here = Scala_Project.here
    override def invoke(session: Session, args: List[Bytes]): List[Bytes] =
      args.map(url => download(url.text).bytes)
  }


  /* repositories */

  val isabelle_repository: Mercurial.Server =
    Mercurial.Server("https://isabelle.in.tum.de/repos/isabelle")

  val afp_repository: Mercurial.Server =
    Mercurial.Server("https://isabelle.sketis.net/repos/afp-devel")

  def official_releases(): List[String] =
    Library.trim_split_lines(
      isabelle_repository.read_file(Path.explode("Admin/Release/official")))
}
