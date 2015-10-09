/*  Title:      Pure/General/file.scala
    Author:     Makarius

File system operations.
*/

package isabelle


import java.io.{BufferedWriter, OutputStreamWriter, FileOutputStream, BufferedOutputStream,
  OutputStream, InputStream, FileInputStream, BufferedInputStream, BufferedReader,
  InputStreamReader, File => JFile, IOException}
import java.nio.file.{StandardCopyOption, Files}
import java.net.{URL, URLDecoder, MalformedURLException}
import java.util.zip.{GZIPInputStream, GZIPOutputStream}
import java.util.regex.Pattern

import scala.collection.mutable
import scala.util.matching.Regex


object File
{
  /* standard path (Cygwin or Posix) */

  def standard_path(path: Path): String = path.expand.implode

  def standard_path(platform_path: String): String =
    if (Platform.is_windows) {
      val Platform_Root = new Regex("(?i)" +
        Pattern.quote(Isabelle_System.cygwin_root()) + """(?:\\+|\z)(.*)""")
      val Drive = new Regex("""([a-zA-Z]):\\*(.*)""")

      platform_path.replace('/', '\\') match {
        case Platform_Root(rest) => "/" + rest.replace('\\', '/')
        case Drive(letter, rest) =>
          "/cygdrive/" + Word.lowercase(letter) +
            (if (rest == "") "" else "/" + rest.replace('\\', '/'))
        case path => path.replace('\\', '/')
      }
    }
    else platform_path

  def standard_path(file: JFile): String = standard_path(file.getPath)

  def standard_url(name: String): String =
    try {
      val url = new URL(name)
      if (url.getProtocol == "file")
        standard_path(URLDecoder.decode(url.getPath, UTF8.charset_name))
      else name
    }
    catch { case _: MalformedURLException => standard_path(name) }


  /* platform path (Windows or Posix) */

  private val Cygdrive = new Regex("/cygdrive/([a-zA-Z])($|/.*)")
  private val Named_Root = new Regex("//+([^/]*)(.*)")

  def platform_path(standard_path: String): String =
    if (Platform.is_windows) {
      val result_path = new StringBuilder
      val rest =
        standard_path match {
          case Cygdrive(drive, rest) =>
            result_path ++= (Word.uppercase(drive) + ":" + JFile.separator)
            rest
          case Named_Root(root, rest) =>
            result_path ++= JFile.separator
            result_path ++= JFile.separator
            result_path ++= root
            rest
          case path if path.startsWith("/") =>
            result_path ++= Isabelle_System.cygwin_root()
            path
          case path => path
        }
      for (p <- space_explode('/', rest) if p != "") {
        val len = result_path.length
        if (len > 0 && result_path(len - 1) != JFile.separatorChar)
          result_path += JFile.separatorChar
        result_path ++= p
      }
      result_path.toString
    }
    else standard_path

  def platform_path(path: Path): String = platform_path(standard_path(path))
  def platform_file(path: Path): JFile = new JFile(platform_path(path))

  def platform_url(raw_path: Path): String =
  {
    val path = raw_path.expand
    require(path.is_absolute)
    val s = platform_path(path).replaceAll(" ", "%20")
    if (!Platform.is_windows) "file://" + s
    else if (s.startsWith("\\\\")) "file:" + s.replace('\\', '/')
    else "file:///" + s.replace('\\', '/')
  }


  /* shell path (bash) */

  def shell_path(path: Path): String = "'" + standard_path(path) + "'"
  def shell_path(file: JFile): String = "'" + standard_path(file) + "'"


  /* directory content */

  def read_dir(dir: Path): List[String] =
  {
    if (!dir.is_dir) error("Bad directory: " + dir.toString)
    val files = dir.file.listFiles
    if (files == null) Nil
    else files.toList.map(_.getName)
  }

  def find_files(dir: Path): Stream[Path] =
    read_dir(dir).toStream.map(name =>
      if (Path.is_wellformed(name)) {
        val path = dir + Path.basic(name)
        path #:: (if (path.is_dir) find_files(path) else Stream.empty)
      }
      else Stream.empty).flatten


  /* read */

  def read(file: JFile): String = Bytes.read(file).toString
  def read(path: Path): String = read(path.file)


  def read_stream(reader: BufferedReader): String =
  {
    val output = new StringBuilder(100)
    var c = -1
    while ({ c = reader.read; c != -1 }) output += c.toChar
    reader.close
    output.toString
  }

  def read_stream(stream: InputStream): String =
   read_stream(new BufferedReader(new InputStreamReader(stream, UTF8.charset)))

  def read_gzip(file: JFile): String =
    read_stream(new GZIPInputStream(new BufferedInputStream(new FileInputStream(file))))

  def read_gzip(path: Path): String = read_gzip(path.file)


  /* read lines */

  def read_lines(reader: BufferedReader, progress: String => Unit): List[String] =
  {
    val result = new mutable.ListBuffer[String]
    var line: String = null
    while ({ line = try { reader.readLine} catch { case _: IOException => null }; line != null }) {
      progress(line)
      result += line
    }
    reader.close
    result.toList
  }


  /* try_read */

  def try_read(paths: Seq[Path]): String =
  {
    val buf = new StringBuilder
    for (path <- paths if path.is_file) {
      buf.append(read(path))
      buf.append('\n')
    }
    buf.toString
  }


  /* write */

  def write_file(file: JFile, text: Iterable[CharSequence],
    make_stream: OutputStream => OutputStream)
  {
    val stream = make_stream(new FileOutputStream(file))
    val writer = new BufferedWriter(new OutputStreamWriter(stream, UTF8.charset))
    try { text.iterator.foreach(writer.append(_)) }
    finally { writer.close }
  }

  def write(file: JFile, text: Iterable[CharSequence]): Unit = write_file(file, text, (s) => s)
  def write(file: JFile, text: CharSequence): Unit = write(file, List(text))
  def write(path: Path, text: Iterable[CharSequence]): Unit = write(path.file, text)
  def write(path: Path, text: CharSequence): Unit = write(path.file, text)

  def write_gzip(file: JFile, text: Iterable[CharSequence]): Unit =
    write_file(file, text, (s: OutputStream) => new GZIPOutputStream(new BufferedOutputStream(s)))
  def write_gzip(file: JFile, text: CharSequence): Unit = write_gzip(file, List(text))
  def write_gzip(path: Path, text: Iterable[CharSequence]): Unit = write_gzip(path.file, text)
  def write_gzip(path: Path, text: CharSequence): Unit = write_gzip(path.file, text)

  def write_backup(path: Path, text: CharSequence)
  {
    path.file renameTo path.backup.file
    File.write(path, text)
  }

  def write_backup2(path: Path, text: CharSequence)
  {
    path.file renameTo path.backup2.file
    File.write(path, text)
  }


  /* copy */

  def eq(file1: JFile, file2: JFile): Boolean =
    try { java.nio.file.Files.isSameFile(file1.toPath, file2.toPath) }
    catch { case ERROR(_) => false }

  def copy(src: JFile, dst: JFile)
  {
    val target = if (dst.isDirectory) new JFile(dst, src.getName) else dst
    if (!eq(src, target))
      Files.copy(src.toPath, target.toPath,
        StandardCopyOption.COPY_ATTRIBUTES,
        StandardCopyOption.REPLACE_EXISTING)
  }

  def copy(path1: Path, path2: Path): Unit = copy(path1.file, path2.file)
}
