/*  Title:      Pure/System/standard_system.scala
    Author:     Makarius

Standard system operations, with basic Cygwin/Posix compatibility.
*/

package isabelle

import java.util.regex.Pattern
import java.util.Locale
import java.io.{BufferedWriter, OutputStreamWriter, FileOutputStream,
  BufferedInputStream, FileInputStream, BufferedReader, InputStreamReader,
  File, IOException}

import scala.io.Source
import scala.util.matching.Regex
import scala.collection.mutable


object Standard_System
{
  val charset = "UTF-8"


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


  /* basic file operations */

  def with_tmp_file[A](prefix: String)(body: File => A): A =
  {
    val file = File.createTempFile(prefix, null)
    try { body(file) } finally { file.delete }
  }

  def read_file(file: File): String =
  {
    val buf = new StringBuilder(file.length.toInt)
    val reader = new BufferedReader(new InputStreamReader(new FileInputStream(file), charset))
    var c = reader.read
    while (c != -1) {
      buf.append(c.toChar)
      c = reader.read
    }
    reader.close
    buf.toString
  }

  def write_file(file: File, text: CharSequence)
  {
    val writer = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(file), charset))
    try { writer.append(text) }
    finally { writer.close }
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

    try { proc.start }
    catch { case e: IOException => error(e.getMessage) }
  }

  def process_output(proc: Process): (String, Int) =
  {
    proc.getOutputStream.close
    val output = Source.fromInputStream(proc.getInputStream, charset).mkString  // FIXME
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
}


class Standard_System
{
  val platform_root = if (Platform.is_windows) Cygwin.check_root() else "/"
  override def toString = platform_root


  /* jvm_path */

  private val Cygdrive = new Regex("/cygdrive/([a-zA-Z])($|/.*)")

  def jvm_path(posix_path: String): String =
    if (Platform.is_windows) {
      val result_path = new StringBuilder
      val rest =
        posix_path match {
          case Cygdrive(drive, rest) =>
            result_path ++= (drive + ":" + File.separator)
            rest
          case path if path.startsWith("/") =>
            result_path ++= platform_root
            path
          case path => path
        }
      for (p <- rest.split("/") if p != "") {
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
}
