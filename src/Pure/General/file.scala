/*  Title:      Pure/General/file.scala
    Author:     Makarius

File system operations.
*/

package isabelle


import java.io.{BufferedWriter, OutputStreamWriter, FileOutputStream, BufferedOutputStream,
  InputStream, FileInputStream, BufferedReader, InputStreamReader, File => JFile, FileFilter}
import java.util.zip.GZIPOutputStream

import scala.collection.mutable


object File
{
  /* read */

  def read(reader: BufferedReader): String =
  {
    val output = new StringBuilder(100)
    var c = -1
    while ({ c = reader.read; c != -1 }) output += c.toChar
    reader.close
    output.toString
  }

  def read(stream: InputStream): String =
    read(new BufferedReader(new InputStreamReader(stream, Standard_System.charset)))

  def read(file: JFile): String = read(new FileInputStream(file))

  def read(path: Path): String = read(path.file)


  /* write */

  private def write_file(file: JFile, text: CharSequence, gzip: Boolean)
  {
    val stream1 = new FileOutputStream(file)
    val stream2 = if (gzip) new GZIPOutputStream(new BufferedOutputStream(stream1)) else stream1
    val writer = new BufferedWriter(new OutputStreamWriter(stream2, Standard_System.charset))
    try { writer.append(text) }
    finally { writer.close }
  }

  def write(file: JFile, text: CharSequence): Unit = write_file(file, text, false)
  def write(path: Path, text: CharSequence): Unit = write(path.file, text)

  def write_gzip(file: JFile, text: CharSequence): Unit = write_file(file, text, true)
  def write_gzip(path: Path, text: CharSequence): Unit = write_gzip(path.file, text)


  /* copy */

  def eq(file1: JFile, file2: JFile): Boolean =
    file1.getCanonicalPath == file2.getCanonicalPath  // FIXME prefer java.nio.file.Files.isSameFile of Java 1.7

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


  /* misc */

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

  // FIXME handle (potentially cyclic) directory graph
  def find_files(start: JFile, ok: JFile => Boolean): List[JFile] =
  {
    val files = new mutable.ListBuffer[JFile]
    val filter = new FileFilter { def accept(entry: JFile) = entry.isDirectory || ok(entry) }
    def find_entry(entry: JFile)
    {
      if (ok(entry)) files += entry
      if (entry.isDirectory) entry.listFiles(filter).foreach(find_entry)
    }
    find_entry(start)
    files.toList
  }
}

