/*  Title:      Pure/System/isabelle_system.scala
    Author:     Makarius

Miscellaneous Isabelle system operations.
*/

package isabelle


import java.util.{Map => JMap}
import java.io.{File => JFile, IOException}
import java.nio.file.{Path => JPath, Files, SimpleFileVisitor, FileVisitResult,
  StandardCopyOption, FileSystemException}
import java.nio.file.attribute.BasicFileAttributes


object Isabelle_System
{
  /* settings */

  def settings(): JMap[String, String] = isabelle.setup.Environment.settings()

  def getenv(name: String, env: JMap[String, String] = settings()): String =
    Option(env.get(name)).getOrElse("")

  def getenv_strict(name: String, env: JMap[String, String] = settings()): String =
    proper_string(getenv(name, env)) getOrElse
      error("Undefined Isabelle environment variable: " + quote(name))


  /* services */

  abstract class Service

  @volatile private var _services: Option[List[Class[Service]]] = None

  def services(): List[Class[Service]] =
  {
    if (_services.isEmpty) init()  // unsynchronized check
    _services.get
  }

  def make_services[C](c: Class[C]): List[C] =
    for { c1 <- services() if Library.is_subclass(c1, c) }
      yield c1.getDeclaredConstructor().newInstance().asInstanceOf[C]


  /* init settings + services */

  def init(isabelle_root: String = "", cygwin_root: String = ""): Unit =
  {
    isabelle.setup.Environment.init(isabelle_root, cygwin_root)
    synchronized {
      if (_services.isEmpty) {
        val variable = "ISABELLE_SCALA_SERVICES"
        val services =
          for (name <- space_explode(':', getenv_strict(variable)))
            yield {
              def err(msg: String): Nothing =
                error("Bad entry " + quote(name) + " in " + variable + "\n" + msg)
              try { Class.forName(name).asInstanceOf[Class[Service]] }
              catch {
                case _: ClassNotFoundException => err("Class not found")
                case exn: Throwable => err(Exn.message(exn))
              }
            }
        _services = Some(services)
      }
    }
  }


  /* getetc -- static distribution parameters */

  def getetc(name: String, root: Path = Path.ISABELLE_HOME): Option[String] =
  {
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
    getetc("ISABELLE_ID", root = root) orElse Mercurial.archive_id(root) getOrElse {
      if (Mercurial.is_repository(root)) Mercurial.repository(root).parent()
      else error("Failed to identify Isabelle distribution " + root)
    }

  object Isabelle_Id extends Scala.Fun_String("isabelle_id")
  {
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

  def identification(): String = "Isabelle/" + isabelle_id() + isabelle_heading()


  /** file-system operations **/

  /* scala functions */

  private def apply_paths(args: List[String], fun: List[Path] => Unit): List[String] =
    { fun(args.map(Path.explode)); Nil }

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

  def make_directory(path: Path): Path =
  {
    if (!path.is_dir) {
      try { Files.createDirectories(path.file.toPath) }
      catch { case ERROR(_) => error("Failed to create directory: " + path.absolute) }
    }
    path
  }

  def new_directory(path: Path): Path =
    if (path.is_dir) error("Directory already exists: " + path.absolute)
    else make_directory(path)

  def copy_dir(dir1: Path, dir2: Path): Unit =
  {
    val res = bash("cp -a " + File.bash_path(dir1) + " " + File.bash_path(dir2))
    if (!res.ok) {
      cat_error("Failed to copy directory " + dir1.absolute + " to " + dir2.absolute, res.err)
    }
  }


  object Make_Directory extends Scala.Fun_Strings("make_directory")
  {
    val here = Scala_Project.here
    def apply(args: List[String]): List[String] = apply_paths1(args, make_directory)
  }

  object Copy_Dir extends Scala.Fun_Strings("copy_dir")
  {
    val here = Scala_Project.here
    def apply(args: List[String]): List[String] = apply_paths2(args, copy_dir)
  }


  /* copy files */

  def copy_file(src: JFile, dst: JFile): Unit =
  {
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
            File.path(src).absolute + " to " + File.path(dst).absolute, msg)
      }
    }
  }

  def copy_file(src: Path, dst: Path): Unit = copy_file(src.file, dst.file)

  def copy_file_base(base_dir: Path, src: Path, target_dir: Path): Unit =
  {
    val src1 = src.expand
    val src1_dir = src1.dir
    if (!src1.starts_basic) error("Illegal path specification " + src1 + " beyond base directory")
    copy_file(base_dir + src1, Isabelle_System.make_directory(target_dir + src1_dir))
  }


  object Copy_File extends Scala.Fun_Strings("copy_file")
  {
    val here = Scala_Project.here
    def apply(args: List[String]): List[String] = apply_paths2(args, copy_file)
  }

  object Copy_File_Base extends Scala.Fun_Strings("copy_file_base")
  {
    val here = Scala_Project.here
    def apply(args: List[String]): List[String] = apply_paths3(args, copy_file_base)
  }


  /* move files */

  def move_file(src: JFile, dst: JFile): Unit =
  {
    val target = if (dst.isDirectory) new JFile(dst, src.getName) else dst
    if (!File.eq(src, target))
      Files.move(src.toPath, target.toPath, StandardCopyOption.REPLACE_EXISTING)
  }

  def move_file(src: Path, dst: Path): Unit = move_file(src.file, dst.file)


  /* symbolic link */

  def symlink(src: Path, dst: Path, force: Boolean = false): Unit =
  {
    val src_file = src.file
    val dst_file = dst.file
    val target = if (dst_file.isDirectory) new JFile(dst_file, src_file.getName) else dst_file

    if (force) target.delete

    def cygwin_link(): Unit =
      isabelle.setup.Environment.cygwin_link(File.standard_path(src), target)

    try { Files.createSymbolicLink(target.toPath, src_file.toPath) }
    catch {
      case _: UnsupportedOperationException if Platform.is_windows => cygwin_link()
      case _: FileSystemException if Platform.is_windows => cygwin_link()
    }
  }


  /* tmp files */

  def isabelle_tmp_prefix(): JFile =
  {
    val path = Path.explode("$ISABELLE_TMP_PREFIX")
    path.file.mkdirs  // low-level mkdirs to avoid recursion via Isabelle environment
    File.platform_file(path)
  }

  def tmp_file(name: String, ext: String = "", base_dir: JFile = isabelle_tmp_prefix()): JFile =
  {
    val suffix = if (ext == "") "" else "." + ext
    val file = Files.createTempFile(base_dir.toPath, name, suffix).toFile
    file.deleteOnExit
    file
  }

  def with_tmp_file[A](name: String, ext: String = "")(body: Path => A): A =
  {
    val file = tmp_file(name, ext)
    try { body(File.path(file)) } finally { file.delete }
  }


  /* tmp dirs */

  def rm_tree(root: JFile): Unit =
  {
    root.delete
    if (root.isDirectory) {
      Files.walkFileTree(root.toPath,
        new SimpleFileVisitor[JPath] {
          override def visitFile(file: JPath, attrs: BasicFileAttributes): FileVisitResult =
          {
            try { Files.deleteIfExists(file) }
            catch { case _: IOException => }
            FileVisitResult.CONTINUE
          }

          override def postVisitDirectory(dir: JPath, e: IOException): FileVisitResult =
          {
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

  object Rm_Tree extends Scala.Fun_Strings("rm_tree")
  {
    val here = Scala_Project.here
    def apply(args: List[String]): List[String] = apply_paths1(args, rm_tree)
  }

  def tmp_dir(name: String, base_dir: JFile = isabelle_tmp_prefix()): JFile =
  {
    val dir = Files.createTempDirectory(base_dir.toPath, name).toFile
    dir.deleteOnExit
    dir
  }

  def with_tmp_dir[A](name: String)(body: Path => A): A =
  {
    val dir = tmp_dir(name)
    try { body(File.path(dir)) } finally { rm_tree(dir) }
  }


  /* quasi-atomic update of directory */

  def update_directory(dir: Path, f: Path => Unit): Unit =
  {
    val new_dir = dir.ext("new")
    val old_dir = dir.ext("old")

    rm_tree(new_dir)
    rm_tree(old_dir)

    f(new_dir)

    if (dir.is_dir) move_file(dir, old_dir)
    move_file(new_dir, dir)
    rm_tree(old_dir)
  }



  /** external processes **/

  /* GNU bash */

  def bash(script: String,
    cwd: JFile = null,
    env: JMap[String, String] = settings(),
    redirect: Boolean = false,
    progress_stdout: String => Unit = (_: String) => (),
    progress_stderr: String => Unit = (_: String) => (),
    watchdog: Option[Bash.Watchdog] = None,
    strict: Boolean = true,
    cleanup: () => Unit = () => ()): Process_Result =
  {
    Bash.process(script, cwd = cwd, env = env, redirect = redirect, cleanup = cleanup).
      result(progress_stdout = progress_stdout, progress_stderr = progress_stderr,
        watchdog = watchdog, strict = strict)
  }

  private lazy val gnutar_check: Boolean =
    try { bash("tar --version").check.out.containsSlice("GNU tar") || error("") }
    catch { case ERROR(_) => false }

  def gnutar(
    args: String,
    dir: Path = Path.current,
    original_owner: Boolean = false,
    strip: Int = 0,
    redirect: Boolean = false): Process_Result =
  {
    val options =
      (if (dir.is_current) "" else "-C " + File.bash_path(dir) + " ") +
      (if (original_owner) "" else "--owner=root --group=staff ") +
      (if (strip <= 0) "" else "--strip-components=" + strip + " ")

    if (gnutar_check) bash("tar " + options + args, redirect = redirect)
    else error("Expected to find GNU tar executable")
  }

  def require_command(cmd: String, test: String = "--version"): Unit =
  {
    if (!bash(Bash.string(cmd) + " " + test).ok) error("Missing system command: " + quote(cmd))
  }

  def hostname(): String = bash("hostname -s").check.out

  def open(arg: String): Unit =
    bash("exec \"$ISABELLE_OPEN\" " + Bash.string(arg) + " >/dev/null 2>/dev/null &")

  def pdf_viewer(arg: Path): Unit =
    bash("exec \"$PDF_VIEWER\" " + File.bash_path(arg) + " >/dev/null 2>/dev/null &")

  def open_external_file(name: String): Boolean =
  {
    val ext = Library.take_suffix((c: Char) => c != '.', name.toList)._2.mkString
    val external =
      ext.nonEmpty &&
      Library.space_explode(':', getenv("ISABELLE_EXTERNAL_FILES")).contains(ext)
    if (external) {
      if (ext == "pdf" && Path.is_wellformed(name)) pdf_viewer(Path.explode(name))
      else open(name)
    }
    external
  }

  def export_isabelle_identifier(isabelle_identifier: String): String =
    if (isabelle_identifier == "") ""
    else "export ISABELLE_IDENTIFIER=" + Bash.string(isabelle_identifier) + "\n"


  /** Isabelle resources **/

  /* repository clone with Admin */

  def admin(): Boolean = Path.explode("~~/Admin").is_dir


  /* default logic */

  def default_logic(args: String*): String =
  {
    args.find(_ != "") match {
      case Some(logic) => logic
      case None => getenv_strict("ISABELLE_LOGIC")
    }
  }


  /* download file */

  def download(url_name: String, progress: Progress = new Progress): HTTP.Content =
  {
    val url = Url(url_name)
    progress.echo("Getting " + quote(url_name))
    try { HTTP.Client.get(url) }
    catch { case ERROR(msg) => cat_error("Failed to download " + quote(url_name), msg) }
  }

  def download_file(url_name: String, file: Path, progress: Progress = new Progress): Unit =
    Bytes.write(file, download(url_name, progress = progress).bytes)

  object Download extends Scala.Fun("download", thread = true)
  {
    val here = Scala_Project.here
    override def invoke(args: List[Bytes]): List[Bytes] =
      args match { case List(url) => List(download(url.text).bytes) }
  }


  /* repositories */

  val isabelle_repository: Mercurial.Server =
    Mercurial.Server("https://isabelle.sketis.net/repos/isabelle")

  val afp_repository: Mercurial.Server =
    Mercurial.Server("https://isabelle.sketis.net/repos/afp-devel")

  def official_releases(): List[String] =
    Library.trim_split_lines(
      isabelle_repository.read_file(Path.explode("Admin/Release/official")))
}
