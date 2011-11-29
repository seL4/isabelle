/*  Title:      Pure/System/standard_system.scala
    Module:     PIDE
    Author:     Makarius

Standard system operations, with basic Cygwin/Posix compatibility.
*/

package isabelle

import java.lang.System
import java.util.zip.{ZipEntry, ZipInputStream}
import java.util.regex.Pattern
import java.util.Locale
import java.net.URL
import java.io.{BufferedWriter, OutputStreamWriter, FileOutputStream, BufferedOutputStream,
  BufferedInputStream, InputStream, FileInputStream, BufferedReader, InputStreamReader,
  File, FileFilter, IOException}
import java.nio.charset.Charset

import scala.io.{Source, Codec}
import scala.util.matching.Regex
import scala.collection.mutable


object Standard_System
{
  /* UTF-8 charset */

  val charset_name: String = "UTF-8"
  val charset: Charset = Charset.forName(charset_name)
  def codec(): Codec = Codec(charset)

  def string_bytes(s: String): Array[Byte] = s.getBytes(charset)


  /* permissive UTF-8 decoding */

  // see also http://en.wikipedia.org/wiki/UTF-8#Description
  // overlong encodings enable byte-stuffing

  def decode_permissive_utf8(text: CharSequence): String =
  {
    val buf = new java.lang.StringBuilder(text.length)
    var code = -1
    var rest = 0
    def flush()
    {
      if (code != -1) {
        if (rest == 0 && Character.isValidCodePoint(code))
          buf.appendCodePoint(code)
        else buf.append('\uFFFD')
        code = -1
        rest = 0
      }
    }
    def init(x: Int, n: Int)
    {
      flush()
      code = x
      rest = n
    }
    def push(x: Int)
    {
      if (rest <= 0) init(x, -1)
      else {
        code <<= 6
        code += x
        rest -= 1
      }
    }
    for (i <- 0 until text.length) {
      val c = text.charAt(i)
      if (c < 128) { flush(); buf.append(c) }
      else if ((c & 0xC0) == 0x80) push(c & 0x3F)
      else if ((c & 0xE0) == 0xC0) init(c & 0x1F, 1)
      else if ((c & 0xF0) == 0xE0) init(c & 0x0F, 2)
      else if ((c & 0xF8) == 0xF0) init(c & 0x07, 3)
    }
    flush()
    buf.toString
  }

  private class Decode_Chars(decode: String => String,
    buffer: Array[Byte], start: Int, end: Int) extends CharSequence
  {
    def length: Int = end - start
    def charAt(i: Int): Char = (buffer(start + i).asInstanceOf[Int] & 0xFF).asInstanceOf[Char]
    def subSequence(i: Int, j: Int): CharSequence =
      new Decode_Chars(decode, buffer, start + i, start + j)

    // toString with adhoc decoding: abuse of CharSequence interface
    override def toString: String = decode(decode_permissive_utf8(this))
  }

  def decode_chars(decode: String => String,
    buffer: Array[Byte], start: Int, end: Int): CharSequence =
  {
    require(0 <= start && start <= end && end <= buffer.length)
    new Decode_Chars(decode, buffer, start, end)
  }


  /* basic file operations */

  def slurp(reader: BufferedReader): String =
  {
    val output = new StringBuilder(100)
    var c = -1
    while ({ c = reader.read; c != -1 }) output += c.toChar
    reader.close
    output.toString
  }

  def slurp(stream: InputStream): String =
    slurp(new BufferedReader(new InputStreamReader(stream, charset)))

  def read_file(file: File): String = slurp(new FileInputStream(file))

  def write_file(file: File, text: CharSequence)
  {
    val writer =
      new BufferedWriter(new OutputStreamWriter(new FileOutputStream(file), charset))
    try { writer.append(text) }
    finally { writer.close }
  }

  def with_tmp_file[A](prefix: String)(body: File => A): A =
  {
    val file = File.createTempFile(prefix, null)
    file.deleteOnExit
    try { body(file) } finally { file.delete }
  }

  // FIXME handle (potentially cyclic) directory graph
  def find_files(start: File, ok: File => Boolean): List[File] =
  {
    val files = new mutable.ListBuffer[File]
    val filter = new FileFilter { def accept(entry: File) = entry.isDirectory || ok(entry) }
    def find_entry(entry: File)
    {
      if (ok(entry)) files += entry
      if (entry.isDirectory) entry.listFiles(filter).foreach(find_entry)
    }
    find_entry(start)
    files.toList
  }


  /* shell processes */

  def raw_execute(cwd: File, env: Map[String, String], redirect: Boolean, args: String*): Process =
  {
    val cmdline = new java.util.LinkedList[String]
    for (s <- args) cmdline.add(s)

    val proc = new ProcessBuilder(cmdline)
    if (cwd != null) proc.directory(cwd)
    if (env != null) {
      proc.environment.clear
      for ((x, y) <- env) proc.environment.put(x, y)
    }
    proc.redirectErrorStream(redirect)
    proc.start
  }

  def process_output(proc: Process): (String, Int) =
  {
    proc.getOutputStream.close
    val output = slurp(proc.getInputStream)
    val rc =
      try { proc.waitFor }
      finally {
        proc.getInputStream.close
        proc.getErrorStream.close
        proc.destroy
        Thread.interrupted
      }
    (output, rc)
  }

  def raw_exec(cwd: File, env: Map[String, String], redirect: Boolean, args: String*)
    : (String, Int) = process_output(raw_execute(cwd, env, redirect, args: _*))


  /* unpack zip archive -- platform file-system */

  def unzip(url: URL, root: File)
  {
    import scala.collection.JavaConversions._

    val buffer = new Array[Byte](4096)

    val zip_stream = new ZipInputStream(new BufferedInputStream(url.openStream))
    var entry: ZipEntry = null
    try {
      while ({ entry = zip_stream.getNextEntry; entry != null }) {
        val file = new File(root, entry.getName.replace('/', File.separatorChar))
        val dir = file.getParentFile
        if (dir != null && !dir.isDirectory && !dir.mkdirs)
          error("Failed to create directory: " + dir)

        var len = 0
        val out_stream = new BufferedOutputStream(new FileOutputStream(file))
        try {
          while ({ len = zip_stream.read(buffer); len != -1 })
            out_stream.write(buffer, 0, len)
        }
        finally { out_stream.close }
      }
    }
    finally { zip_stream.close }
  }


  /* unpack tar archive -- POSIX file-system */

  def posix_untar(url: URL, root: File, gunzip: Boolean = false,
    tar: String = "tar", gzip: String = "", progress: Int => Unit = _ => ()): String =
  {
    if (!root.isDirectory && !root.mkdirs)
      error("Failed to create root directory: " + root)

    val connection = url.openConnection

    val length = connection.getContentLength.toLong
    require(length >= 0L)

    val stream = new BufferedInputStream(connection.getInputStream)
    val progress_stream = new InputStream {
      private val total = length max 1L
      private var index = 0L
      private var percentage = 0L
      override def read(): Int =
      {
        val c = stream.read
        if (c != -1) {
          index += 100
          val p = index / total
          if (percentage != p) { percentage = p; progress(percentage.toInt) }
        }
        c
      }
      override def available(): Int = stream.available
      override def close() { stream.close }
    }

    val cmdline =
      List(tar, "-o", "-x", "-f-") :::
        (if (!gunzip) Nil else if (gzip == "") List("-z") else List("-I", gzip))

    val proc = raw_execute(root, null, false, cmdline:_*)
    val stdout = Simple_Thread.future("tar_stdout") { slurp(proc.getInputStream) }
    val stderr = Simple_Thread.future("tar_stderr") { slurp(proc.getErrorStream) }
    val stdin = new BufferedOutputStream(proc.getOutputStream)

    try {
      var c = -1
      val io_err =
        try { while ({ c = progress_stream.read; c != -1 }) stdin.write(c); false }
        catch { case e: IOException => true }
      stdin.close

      val rc = try { proc.waitFor } finally { Thread.interrupted }
      if (io_err || rc != 0) error(stderr.join.trim) else stdout.join
    }
    finally {
      progress_stream.close
      stdin.close
      proc.destroy
    }
  }
}


class Standard_System
{
  /* platform_root */

  val platform_root = if (Platform.is_windows) Cygwin.check_root() else "/"


  /* jvm_path */

  private val Cygdrive = new Regex("/cygdrive/([a-zA-Z])($|/.*)")
  private val Named_Root = new Regex("//+([^/]*)(.*)")

  def jvm_path(posix_path: String): String =
    if (Platform.is_windows) {
      val result_path = new StringBuilder
      val rest =
        posix_path match {
          case Cygdrive(drive, rest) =>
            result_path ++= (drive.toUpperCase(Locale.ENGLISH) + ":" + File.separator)
            rest
          case Named_Root(root, rest) =>
            result_path ++= File.separator
            result_path ++= File.separator
            result_path ++= root
            rest
          case path if path.startsWith("/") =>
            result_path ++= platform_root
            path
          case path => path
        }
      for (p <- space_explode('/', rest) if p != "") {
        val len = result_path.length
        if (len > 0 && result_path(len - 1) != File.separatorChar)
          result_path += File.separatorChar
        result_path ++= p
      }
      result_path.toString
    }
    else posix_path


  /* posix_path */

  private val Platform_Root = new Regex("(?i)" +
    Pattern.quote(platform_root) + """(?:\\+|\z)(.*)""")

  private val Drive = new Regex("""([a-zA-Z]):\\*(.*)""")

  def posix_path(jvm_path: String): String =
    if (Platform.is_windows) {
      jvm_path.replace('/', '\\') match {
        case Platform_Root(rest) => "/" + rest.replace('\\', '/')
        case Drive(letter, rest) =>
          "/cygdrive/" + letter.toLowerCase(Locale.ENGLISH) +
            (if (rest == "") "" else "/" + rest.replace('\\', '/'))
        case path => path.replace('\\', '/')
      }
    }
    else jvm_path


  /* this_java executable */

  def this_java(): String =
  {
    val java_home = System.getProperty("java.home")
    val java_exe =
      if (Platform.is_windows) new File(java_home + "\\bin\\java.exe")
      else new File(java_home + "/bin/java")
    if (!java_exe.isFile) error("Expected this Java executable: " + java_exe.toString)
    posix_path(java_exe.getAbsolutePath)
  }
}
