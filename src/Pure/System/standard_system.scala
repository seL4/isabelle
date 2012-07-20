/*  Title:      Pure/System/standard_system.scala
    Module:     PIDE
    Author:     Makarius

Standard system operations, with basic Cygwin/Posix compatibility.
*/

package isabelle

import java.lang.System
import java.util.regex.Pattern
import java.util.Locale
import java.net.URL
import java.io.{BufferedWriter, OutputStreamWriter, FileOutputStream, BufferedOutputStream,
  BufferedInputStream, InputStream, FileInputStream, BufferedReader, InputStreamReader,
  File => JFile, FileFilter, IOException}
import java.nio.charset.Charset
import java.util.zip.GZIPOutputStream

import scala.io.Codec
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

  def read_file(file: JFile): String = slurp(new FileInputStream(file))

  def write_file(file: JFile, text: CharSequence, zip: Boolean = false)
  {
    val stream1 = new FileOutputStream(file)
    val stream2 = if (zip) new GZIPOutputStream(new BufferedOutputStream(stream1)) else stream1
    val writer = new BufferedWriter(new OutputStreamWriter(stream2, charset))
    try { writer.append(text) }
    finally { writer.close }
  }

  def eq_file(file1: JFile, file2: JFile): Boolean =
    file1.getCanonicalPath == file2.getCanonicalPath  // FIXME prefer java.nio.file.Files.isSameFile of Java 1.7

  def copy_file(src: JFile, dst: JFile) =
    if (!eq_file(src, dst)) {
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

  def with_tmp_file[A](prefix: String)(body: JFile => A): A =
  {
    val file = JFile.createTempFile(prefix, null)
    file.deleteOnExit
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


  /* shell processes */

  def raw_execute(cwd: JFile, env: Map[String, String], redirect: Boolean, args: String*): Process =
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

  def raw_exec(cwd: JFile, env: Map[String, String], redirect: Boolean, args: String*)
    : (String, Int) = process_output(raw_execute(cwd, env, redirect, args: _*))


  /* cygwin_root */

  def cygwin_root(): String =
  {
    val cygwin_root1 = System.getenv("CYGWIN_ROOT")
    val cygwin_root2 = System.getProperty("cygwin.root")
    val root =
      if (cygwin_root1 != null && cygwin_root1 != "") cygwin_root1
      else if (cygwin_root2 != null && cygwin_root2 != "") cygwin_root2
      else error("Bad Cygwin installation: unknown root")

    val root_file = new JFile(root)
    if (!new JFile(root_file, "bin\\bash.exe").isFile ||
        !new JFile(root_file, "bin\\env.exe").isFile ||
        !new JFile(root_file, "bin\\tar.exe").isFile)
      error("Bad Cygwin installation: " + quote(root))

    root
  }
}


class Standard_System
{
  /* platform_root */

  val platform_root = if (Platform.is_windows) Standard_System.cygwin_root() else "/"


  /* jvm_path */

  private val Cygdrive = new Regex("/cygdrive/([a-zA-Z])($|/.*)")
  private val Named_Root = new Regex("//+([^/]*)(.*)")

  def jvm_path(posix_path: String): String =
    if (Platform.is_windows) {
      val result_path = new StringBuilder
      val rest =
        posix_path match {
          case Cygdrive(drive, rest) =>
            result_path ++= (drive.toUpperCase(Locale.ENGLISH) + ":" + JFile.separator)
            rest
          case Named_Root(root, rest) =>
            result_path ++= JFile.separator
            result_path ++= JFile.separator
            result_path ++= root
            rest
          case path if path.startsWith("/") =>
            result_path ++= platform_root
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


  /* JDK home of running JVM */

  def this_jdk_home(): String =
  {
    val java_home = System.getProperty("java.home")
    val home = new JFile(java_home)
    val parent = home.getParent
    val jdk_home =
      if (home.getName == "jre" && parent != null &&
          (new JFile(new JFile(parent, "bin"), "javac")).exists) parent
      else java_home
    posix_path(jdk_home)
  }
}
