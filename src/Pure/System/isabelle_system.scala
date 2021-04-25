/*  Title:      Pure/System/isabelle_system.scala
    Author:     Makarius

Fundamental Isabelle system environment: quasi-static module with
optional init operation.
*/

package isabelle


import java.io.{File => JFile, IOException}
import java.nio.file.{Path => JPath, Files, SimpleFileVisitor, FileVisitResult,
  StandardCopyOption, FileSystemException}
import java.nio.file.attribute.BasicFileAttributes

import scala.jdk.CollectionConverters._


object Isabelle_System
{
  /** bootstrap information **/

  def jdk_home(): String =
  {
    val java_home = System.getProperty("java.home", "")
    val home = new JFile(java_home)
    val parent = home.getParent
    if (home.getName == "jre" && parent != null &&
        (new JFile(new JFile(parent, "bin"), "javac")).exists) parent
    else java_home
  }

  def bootstrap_directory(
    preference: String, envar: String, property: String, description: String): String =
  {
    val value =
      proper_string(preference) orElse  // explicit argument
      proper_string(System.getenv(envar)) orElse  // e.g. inherited from running isabelle tool
      proper_string(System.getProperty(property)) getOrElse  // e.g. via JVM application boot process
      error("Unknown " + description + " directory")

    if ((new JFile(value)).isDirectory) value
    else error("Bad " + description + " directory " + quote(value))
  }



  /** implicit settings environment **/

  abstract class Service

  @volatile private var _settings: Option[Map[String, String]] = None
  @volatile private var _services: Option[List[Class[Service]]] = None

  def settings(): Map[String, String] =
  {
    if (_settings.isEmpty) init()  // unsynchronized check
    _settings.get
  }

  def services(): List[Class[Service]] =
  {
    if (_services.isEmpty) init()  // unsynchronized check
    _services.get
  }

  def make_services[C](c: Class[C]): List[C] =
    for { c1 <- services() if Library.is_subclass(c1, c) }
      yield c1.getDeclaredConstructor().newInstance().asInstanceOf[C]

  def init(isabelle_root: String = "", cygwin_root: String = ""): Unit = synchronized
  {
    if (_settings.isEmpty || _services.isEmpty) {
      val isabelle_root1 =
        bootstrap_directory(isabelle_root, "ISABELLE_ROOT", "isabelle.root", "Isabelle root")

      val cygwin_root1 =
        if (Platform.is_windows)
          bootstrap_directory(cygwin_root, "CYGWIN_ROOT", "cygwin.root", "Cygwin root")
        else ""

      if (Platform.is_windows) Cygwin.init(isabelle_root1, cygwin_root1)

      def set_cygwin_root(): Unit =
      {
        if (Platform.is_windows)
          _settings = Some(_settings.getOrElse(Map.empty) + ("CYGWIN_ROOT" -> cygwin_root1))
      }

      set_cygwin_root()

      def default(env: Map[String, String], entry: (String, String)): Map[String, String] =
        if (env.isDefinedAt(entry._1) || entry._2 == "") env
        else env + entry

      val env =
      {
        val temp_windows =
        {
          val temp = if (Platform.is_windows) System.getenv("TEMP") else null
          if (temp != null && temp.contains('\\')) temp else ""
        }
        val user_home = System.getProperty("user.home", "")
        val isabelle_app = System.getProperty("isabelle.app", "")

        default(
          default(
            default(sys.env + ("ISABELLE_JDK_HOME" -> File.standard_path(jdk_home())),
              "TEMP_WINDOWS" -> temp_windows),
            "HOME" -> user_home),
          "ISABELLE_APP" -> "true")
      }

      val settings =
      {
        val dump = JFile.createTempFile("settings", null)
        dump.deleteOnExit
        try {
          val cmd1 =
            if (Platform.is_windows)
              List(cygwin_root1 + "\\bin\\bash", "-l",
                File.standard_path(isabelle_root1 + "\\bin\\isabelle"))
            else
              List(isabelle_root1 + "/bin/isabelle")
          val cmd = cmd1 ::: List("getenv", "-d", dump.toString)

          val (output, rc) = process_output(process(cmd, env = env, redirect = true))
          if (rc != 0) error(output)

          val entries =
            (for (entry <- space_explode('\u0000', File.read(dump)) if entry != "") yield {
              val i = entry.indexOf('=')
              if (i <= 0) entry -> ""
              else entry.substring(0, i) -> entry.substring(i + 1)
            }).toMap
          entries + ("PATH" -> entries("PATH_JVM")) - "PATH_JVM"
        }
        finally { dump.delete }
      }
      _settings = Some(settings)
      set_cygwin_root()

      val variable = "ISABELLE_SCALA_SERVICES"
      val services =
        for (name <- space_explode(':', settings.getOrElse(variable, getenv_error(variable))))
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


  /* getenv -- dynamic process environment */

  private def getenv_error(name: String): Nothing =
    error("Undefined Isabelle environment variable: " + quote(name))

  def getenv(name: String, env: Map[String, String] = settings()): String =
    env.getOrElse(name, "")

  def getenv_strict(name: String, env: Map[String, String] = settings()): String =
    proper_string(getenv(name, env)) getOrElse
      error("Undefined Isabelle environment variable: " + quote(name))

  def cygwin_root(): String = getenv_strict("CYGWIN_ROOT")


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
          cat_error("Failed top copy file " +
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

    try { Files.createSymbolicLink(target.toPath, src_file.toPath) }
    catch {
      case _: UnsupportedOperationException if Platform.is_windows =>
        Cygwin.link(File.standard_path(src), target)
      case _: FileSystemException if Platform.is_windows =>
        Cygwin.link(File.standard_path(src), target)
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

  /* raw process */

  def process(command_line: List[String],
    cwd: JFile = null,
    env: Map[String, String] = settings(),
    redirect: Boolean = false): Process =
  {
    val proc = new ProcessBuilder

    // fragile on Windows:
    // see https://docs.microsoft.com/en-us/cpp/cpp/main-function-command-line-args?view=msvc-160
    proc.command(command_line.asJava)

    if (cwd != null) proc.directory(cwd)
    if (env != null) {
      proc.environment.clear()
      for ((x, y) <- env) proc.environment.put(x, y)
    }
    proc.redirectErrorStream(redirect)
    proc.start
  }

  def process_output(proc: Process): (String, Int) =
  {
    proc.getOutputStream.close()

    val output = File.read_stream(proc.getInputStream)
    val rc =
      try { proc.waitFor }
      finally {
        proc.getInputStream.close()
        proc.getErrorStream.close()
        proc.destroy()
        Exn.Interrupt.dispose()
      }
    (output, rc)
  }

  def process_signal(group_pid: String, signal: String = "0"): Boolean =
  {
    val bash =
      if (Platform.is_windows) List(cygwin_root() + "\\bin\\bash.exe")
      else List("/usr/bin/env", "bash")
    val (_, rc) = process_output(process(bash ::: List("-c", "kill -" + signal + " -" + group_pid)))
    rc == 0
  }


  /* GNU bash */

  def bash(script: String,
    cwd: JFile = null,
    env: Map[String, String] = settings(),
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
    redirect: Boolean = false): Process_Result =
  {
    val options =
      (if (dir.is_current) "" else "-C " + File.bash_path(dir) + " ") +
      (if (original_owner) "" else "--owner=root --group=staff ")

    if (gnutar_check) bash("tar " + options + args, redirect = redirect)
    else error("Expected to find GNU tar executable")
  }

  def require_command(cmds: String*): Unit =
  {
    for (cmd <- cmds) {
      if (!bash(Bash.string(cmd) + " --version").ok) error("Missing system command: " + quote(cmd))
    }
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


  /* components */

  def components(): List[Path] =
    Path.split(getenv_strict("ISABELLE_COMPONENTS"))


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
}
