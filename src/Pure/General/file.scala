/*  Title:      Pure/General/file.scala
    Author:     Makarius

File system operations.
*/

package isabelle


import java.io.{BufferedWriter, OutputStreamWriter, FileOutputStream, BufferedOutputStream,
  OutputStream, InputStream, FileInputStream, BufferedInputStream, BufferedReader,
  InputStreamReader, File => JFile, IOException}
import java.util.zip.{GZIPInputStream, GZIPOutputStream}

import scala.collection.mutable


object File
{
  /* directory content */

  def read_dir(dir: Path): List[String] =
  {
    if (!dir.is_dir) error("Bad directory: " + dir.toString)
    val files = dir.file.listFiles
    if (files == null) Nil
    else files.toList.map(_.getName)
  }

  def find_files(dir: Path): Stream[Path] =
    read_dir(dir).toStream.map(name => {
      val path = dir + Path.basic(name)
      path #:: (if (path.is_dir) find_files(path) else Stream.empty)
    }).flatten


  /* read */

  def read_bytes(file: JFile): Array[Byte] =
  {
    var i = 0
    var m = 0
    val n = file.length.toInt
    val buf = new Array[Byte](n)

    val stream = new FileInputStream(file)
    try {
      do {
        m = stream.read(buf, i, n - i)
        if (m != -1) i += m
      } while (m != -1 && n > i)
    }
    finally { stream.close }
    buf
  }

  def read(file: JFile): String = new String(read_bytes(file), UTF8.charset)
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


  /* copy */

  def eq(file1: JFile, file2: JFile): Boolean =
    try { java.nio.file.Files.isSameFile(file1.toPath, file2.toPath) }
    catch { case ERROR(_) => false }

  def copy(src: JFile, dst: JFile)
  {
    if (!eq(src, dst)) {
      val in = new FileInputStream(src)
      try {
        val out = new FileOutputStream(dst)
        try {
          val buf = new Array[Byte](65536)
          var m = 0
          do {
            m = in.read(buf, 0, buf.length)
            if (m != -1) out.write(buf, 0, m)
          } while (m != -1)
        }
        finally { out.close }
      }
      finally { in.close }
    }
  }

  def copy(path1: Path, path2: Path): Unit = copy(path1.file, path2.file)


  /* tmp files */

  def tmp_file(prefix: String): JFile =
  {
    val file = JFile.createTempFile(prefix, null)
    file.deleteOnExit
    file
  }

  def with_tmp_file[A](prefix: String)(body: JFile => A): A =
  {
    val file = tmp_file(prefix)
    try { body(file) } finally { file.delete }
  }
}

