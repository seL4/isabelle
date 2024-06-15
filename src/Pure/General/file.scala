/*  Title:      Pure/General/file.scala
    Author:     Makarius

File-system operations.
*/

package isabelle


import java.util.{Properties => JProperties}
import java.io.{BufferedWriter, OutputStreamWriter, FileOutputStream, BufferedOutputStream,
  OutputStream, InputStream, FileInputStream, BufferedInputStream, BufferedReader,
  InputStreamReader, File => JFile, IOException}
import java.nio.file.{StandardOpenOption, Path => JPath, Files, SimpleFileVisitor,
  FileVisitOption, FileVisitResult}
import java.nio.file.attribute.{BasicFileAttributes, PosixFilePermission}
import java.net.URI
import java.util.zip.{GZIPInputStream, GZIPOutputStream}
import java.util.EnumSet

import org.tukaani.xz
import com.github.luben.zstd

import scala.collection.mutable


object File {
  /* standard path (Cygwin or Posix) */

  def standard_path(path: Path): String = path.expand.implode

  def standard_path(platform_path: String): String =
    isabelle.setup.Environment.standard_path(platform_path)

  def standard_path(file: JFile): String = standard_path(file.getPath)

  def standard_url(name: String): String =
    try {
      val url = new URI(name).toURL
      if (url.getProtocol == "file" && Url.is_wellformed_file(name)) {
        standard_path(Url.parse_file(name))
      }
      else name
    }
    catch { case exn: Throwable if Url.is_malformed(exn) => standard_path(name) }


  /* platform path (Windows or Posix) */

  def platform_path(standard_path: String): String =
    isabelle.setup.Environment.platform_path(standard_path)

  def platform_path(path: Path): String = platform_path(standard_path(path))
  def platform_file(path: Path): JFile = new JFile(platform_path(path))


  /* symbolic path representation, e.g. "~~/src/Pure/ROOT.ML" */

  def symbolic_path(path: Path): String = {
    val directories = space_explode(':', Isabelle_System.getenv("ISABELLE_DIRECTORIES")).reverse
    val full_name = standard_path(path)
    directories.view.flatMap(a =>
      try {
        val b = standard_path(Path.explode(a))
        if (full_name == b) Some(a)
        else {
          Library.try_unprefix(b + "/", full_name) match {
            case Some(name) => Some(a + "/" + name)
            case None => None
          }
        }
      } catch { case ERROR(_) => None }).headOption.getOrElse(path.implode)
  }


  /* platform files */

  def absolute(file: JFile): JFile = file.toPath.toAbsolutePath.normalize.toFile
  def canonical(file: JFile): JFile = file.getCanonicalFile

  def path(file: JFile): Path = Path.explode(standard_path(file))
  def path(java_path: JPath): Path = path(java_path.toFile)

  def uri(file: JFile): URI = file.toURI
  def uri(path: Path): URI = path.file.toURI

  def url(file: JFile): Url = Url(uri(file))
  def url(path: Path): Url = url(path.file)


  /* adhoc file types */

  def is_ML(s: String): Boolean = s.endsWith(".ML")
  def is_bib(s: String): Boolean = s.endsWith(".bib")
  def is_dll(s: String): Boolean = s.endsWith(".dll")
  def is_exe(s: String): Boolean = s.endsWith(".exe")
  def is_gz(s: String): Boolean = s.endsWith(".gz")
  def is_html(s: String): Boolean = s.endsWith(".html")
  def is_jar(s: String): Boolean = s.endsWith(".jar")
  def is_java(s: String): Boolean = s.endsWith(".java")
  def is_node(s: String): Boolean = s.endsWith(".node")
  def is_pdf(s: String): Boolean = s.endsWith(".pdf")
  def is_png(s: String): Boolean = s.endsWith(".png")
  def is_tar_bz2(s: String): Boolean = s.endsWith(".tar.bz2")
  def is_tar_gz(s: String): Boolean = s.endsWith(".tar.gz")
  def is_tgz(s: String): Boolean = s.endsWith(".tgz")
  def is_thy(s: String): Boolean = s.endsWith(".thy")
  def is_xz(s: String): Boolean = s.endsWith(".xz")
  def is_zip(s: String): Boolean = s.endsWith(".zip")
  def is_zst(s: String): Boolean = s.endsWith(".zst")

  def is_backup(s: String): Boolean = s.endsWith("~") || s.endsWith(".orig")


  /* relative paths */

  def relative_path(base: Path, other: Path): Option[Path] = {
    val base_path = base.java_path
    val other_path = other.java_path
    if (other_path.startsWith(base_path))
      Some(path(base_path.relativize(other_path).toFile))
    else None
  }


  /* bash path */

  def bash_path(path: Path): String = Bash.string(standard_path(path))
  def bash_path(file: JFile): String = Bash.string(standard_path(file))

  def bash_platform_path(path: Path): String = Bash.string(platform_path(path))


  /* directory content */

  def read_dir(dir: Path): List[String] = {
    if (!dir.is_dir) error("No such directory: " + dir.toString)
    val files = dir.file.listFiles
    if (files == null) Nil
    else files.toList.map(_.getName).sorted
  }

  def get_entry(
    dir: Path,
    pred: Path => Boolean = _ => true,
    title: String = ""
  ): Path =
    read_dir(dir).filter(name => pred(dir + Path.basic(name))) match {
      case List(entry) => dir + Path.basic(entry)
      case bad =>
        error("Bad directory content in " + (if (title.nonEmpty) title else dir.toString) +
          "\nexpected a single entry, but found" +
          (if (bad.isEmpty) " nothing"
           else bad.sorted.map(quote).mkString(":\n  ", "\n  ", "")))
    }

  def get_file(dir: Path, title: String = ""): Path =
    get_entry(dir, pred = _.is_file, title = title)

  def get_dir(dir: Path, title: String = ""): Path =
    get_entry(dir, pred = _.is_dir, title = title)

  def find_files(
    start: JFile,
    pred: JFile => Boolean = _ => true,
    include_dirs: Boolean = false,
    follow_links: Boolean = false
  ): List[JFile] = {
    val result = new mutable.ListBuffer[JFile]
    def check(file: JFile): Unit = if (pred(file)) result += file

    if (start.isFile) check(start)
    else if (start.isDirectory) {
      val options =
        if (follow_links) EnumSet.of(FileVisitOption.FOLLOW_LINKS)
        else EnumSet.noneOf(classOf[FileVisitOption])
      Files.walkFileTree(start.toPath, options, Int.MaxValue,
        new SimpleFileVisitor[JPath] {
          override def preVisitDirectory(
            path: JPath,
            attrs: BasicFileAttributes
          ): FileVisitResult = {
            if (include_dirs) check(path.toFile)
            FileVisitResult.CONTINUE
          }
          override def visitFile(
            path: JPath,
            attrs: BasicFileAttributes
          ): FileVisitResult = {
            val file = path.toFile
            if (include_dirs || !file.isDirectory) check(file)
            FileVisitResult.CONTINUE
          }
        }
      )
    }

    result.toList
  }


  /* read */

  def read(file: JFile): String = Bytes.read(file).text
  def read(path: Path): String = read(path.file)


  def read_stream(reader: BufferedReader): String = {
    val output = new StringBuilder(100)
    var c = -1
    while ({ c = reader.read; c != -1 }) output += c.toChar
    reader.close()
    output.toString
  }

  def read_stream(stream: InputStream): String =
    read_stream(new BufferedReader(new InputStreamReader(stream, UTF8.charset)))

  def read_gzip(file: JFile): String =
    read_stream(new GZIPInputStream(new BufferedInputStream(new FileInputStream(file))))
  def read_gzip(path: Path): String = read_gzip(path.file)

  def read_xz(file: JFile): String =
    read_stream(new xz.XZInputStream(new BufferedInputStream(new FileInputStream(file))))
  def read_xz(path: Path): String = read_xz(path.file)

  def read_zstd(file: JFile): String = {
    Zstd.init()
    read_stream(new zstd.ZstdInputStream(new BufferedInputStream(new FileInputStream(file))))
  }
  def read_zstd(path: Path): String = read_zstd(path.file)


  /* read lines */

  def read_line(reader: BufferedReader): Option[String] = {
    val line =
      try { reader.readLine}
      catch { case _: IOException => null }
    Option(line).map(Library.trim_line)
  }

  def read_lines(reader: BufferedReader, progress: String => Unit): List[String] = {
    val result = new mutable.ListBuffer[String]
    var line: Option[String] = None
    while ({ line = read_line(reader); line.isDefined }) {
      progress(line.get)
      result += line.get
    }
    reader.close()
    result.toList
  }


  /* read properties */

  def read_props(path: Path): JProperties = {
    val props = new JProperties
    props.load(Files.newBufferedReader(path.java_path))
    props
  }


  /* write */

  def writer(file: JFile): BufferedWriter =
    new BufferedWriter(new OutputStreamWriter(new FileOutputStream(file), UTF8.charset))

  def write_file(
    file: JFile,
    text: String,
    make_stream: OutputStream => OutputStream
  ): Unit = {
    val stream = make_stream(new FileOutputStream(file))
    using(new BufferedWriter(new OutputStreamWriter(stream, UTF8.charset)))(_.append(text))
  }

  def write(file: JFile, text: String): Unit = write_file(file, text, s => s)
  def write(path: Path, text: String): Unit = write(path.file, text)

  def write_gzip(file: JFile, text: String): Unit =
    write_file(file, text, (s: OutputStream) => new GZIPOutputStream(new BufferedOutputStream(s)))
  def write_gzip(path: Path, text: String): Unit = write_gzip(path.file, text)

  def write_xz(file: JFile, text: String, options: Compress.Options_XZ): Unit =
    File.write_file(file, text,
      s => new xz.XZOutputStream(new BufferedOutputStream(s), options.make))
  def write_xz(file: JFile, text: String): Unit = write_xz(file, text, Compress.Options_XZ())
  def write_xz(path: Path, text: String, options: Compress.Options_XZ): Unit =
    write_xz(path.file, text, options)
  def write_xz(path: Path, text: String): Unit = write_xz(path, text, Compress.Options_XZ())

  def write_zstd(file: JFile, text: String, options: Compress.Options_Zstd): Unit = {
    Zstd.init()
    File.write_file(file, text,
      s => new zstd.ZstdOutputStream(new BufferedOutputStream(s), options.level))
  }
  def write_zstd(file: JFile, text: String): Unit =
    write_zstd(file, text, Compress.Options_Zstd())
  def write_zstd(path: Path, text: String, options: Compress.Options_Zstd): Unit =
    write_zstd(path.file, text, options)
  def write_zstd(path: Path, text: String): Unit =
    write_zstd(path, text, Compress.Options_Zstd())

  def write_backup(path: Path, text: String): Unit = {
    if (path.is_file) Isabelle_System.move_file(path, path.backup)
    write(path, text)
  }

  def write_backup2(path: Path, text: String): Unit = {
    if (path.is_file) Isabelle_System.move_file(path, path.backup2)
    write(path, text)
  }


  /* append */

  def append(file: JFile, text: String): Unit =
    Files.write(file.toPath, UTF8.bytes(text),
      StandardOpenOption.APPEND, StandardOpenOption.CREATE)

  def append(path: Path, text: String): Unit = append(path.file, text)


  /* change */

  def change(
    path: Path,
    init: Boolean = false,
    strict: Boolean = false
  )(f: String => String): Unit = {
    if (!path.is_file && init) write(path, "")
    val x = read(path)
    val y = f(x)
    if (x != y) write(path, y)
    else if (strict) error("Unchanged file: " + path)
  }

  def change_lines(path: Path, init: Boolean = false, strict: Boolean = false)(
      f: List[String] => List[String]): Unit =
    change(path, init = init, strict = strict)(text => cat_lines(f(split_lines(text))))


  /* eq */

  def eq(file1: JFile, file2: JFile): Boolean =
    try { Files.isSameFile(file1.toPath, file2.toPath) }
    catch { case ERROR(_) => false }

  def eq(path1: Path, path2: Path): Boolean = eq(path1.file, path2.file)


  /* eq_content */

  def eq_content(file1: JFile, file2: JFile): Boolean =
    if (eq(file1, file2)) true
    else if (file1.length != file2.length) false
    else SHA1.digest(file1) == SHA1.digest(file2)

  def eq_content(path1: Path, path2: Path): Boolean = eq_content(path1.file, path2.file)


  /* permissions */

  private val restrict_perms: List[PosixFilePermission] =
    List(
      PosixFilePermission.GROUP_READ,
      PosixFilePermission.GROUP_WRITE,
      PosixFilePermission.GROUP_EXECUTE,
      PosixFilePermission.OTHERS_READ,
      PosixFilePermission.OTHERS_WRITE,
      PosixFilePermission.OTHERS_EXECUTE)

  def restrict(path: Path): Unit =
    if (Platform.is_windows) Isabelle_System.chmod("g-rwx,o-rwx", path)
    else {
      val perms = Files.getPosixFilePermissions(path.java_path)
      var perms_changed = false
      for (p <- restrict_perms if perms.contains(p)) {
        perms.remove(p)
        perms_changed = true
      }
      if (perms_changed) Files.setPosixFilePermissions(path.java_path, perms)
    }

  def is_executable(path: Path): Boolean = {
    if (Platform.is_windows) Isabelle_System.bash("test -x " + bash_path(path)).check.ok
    else path.file.canExecute
  }

  def set_executable(path: Path, reset: Boolean = false): Unit = {
    if (Platform.is_windows) Isabelle_System.chmod(if (reset) "a-x" else "a+x", path)
    else path.file.setExecutable(!reset, false)
  }


  /* content */

  def content(path: Path, content: Bytes): Content = new Content(path, content)
  def content(path: Path, content: String): Content = new Content(path, Bytes(content))
  def content(path: Path, content: XML.Body): Content_XML = new Content_XML(path, content)

  final class Content private[File](val path: Path, val content: Bytes) {
    override def toString: String = path.toString

    def write(dir: Path, ssh: SSH.System = SSH.Local): Unit = {
      val full_path = dir + path
      ssh.make_directory(ssh.expand_path(full_path).dir)
      ssh.write_bytes(full_path, content)
    }
  }

  final class Content_XML private[File](val path: Path, val content: XML.Body) {
    override def toString: String = path.toString

    def output(out: XML.Body => String): Content = new Content(path, Bytes(out(content)))
  }


  /* strict file size */

  def size(path: Path): Long = path.check_file.file.length
  def space(path: Path): Space = Space.bytes(size(path))
}
