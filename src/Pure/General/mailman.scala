/*  Title:      Pure/General/mailman.scala
    Author:     Makarius

Support for Mailman list servers.
*/

package isabelle


import java.net.URL

import scala.annotation.tailrec
import scala.util.matching.Regex
import scala.util.matching.Regex.Match


object Mailman
{
  /* mailing list messages */

  sealed case class Message(
    name: String,
    date: Date,
    title: String,
    author_name: String,
    author_address: String,
    body: String)
  {
    def print: String =
      name + "\n" + date + "\n" + quote(author_name) + "\n" + "<" + author_address + ">"
  }

  def message_match(lines: List[String], re: Regex): Option[Match] =
    lines.flatMap(re.findFirstMatchIn(_)).headOption

  class Message_Chunk(bg: String, en: String = "")
  {
    def unapply(lines: List[String]): Option[List[String]] =
      lines.dropWhile(_ != bg) match {
        case Nil => None
        case _ :: rest =>
          if (en.isEmpty) Some(rest)
          else {
            val res = rest.takeWhile(_ != en)
            if (rest.drop(res.length).isEmpty) None else Some(res)
          }
      }
    def get(lines: List[String]): List[String] =
      unapply(lines) getOrElse error("Missing " + bg + (if (en.nonEmpty) " " + en else ""))
  }

  object Address
  {
    def anchor(s: String): String = """<a href="[^"]*">""" + s + """</a>"""
    def angl(s: String): String = """&lt;""" + s + """&gt;"""
    def quot(s: String): String = """&quot;""" + s + """&quot;"""
    def paren(s: String): String = """\(""" + s + """\)"""
    val adr = """([^<>]*? at [^<>]*?)"""
    val any = """([^<>]*?)"""
    val spc = """\s*"""

    val Name1 = quot(anchor(any)).r
    val Name2 = quot(any).r
    val Name_Adr1 = (quot(anchor(any)) + spc + angl(anchor(adr))).r
    val Name_Adr2 = (quot(any) + spc + angl(anchor(adr))).r
    val Name_Adr3 = (anchor(any) + spc + angl(anchor(adr))).r
    val Name_Adr4 = (any + spc + angl(anchor(adr))).r
    val Adr_Name1 = (angl(anchor(adr)) + spc + paren(any)).r
    val Adr_Name2 = (anchor(adr) + spc + paren(any)).r
    val Adr1 = angl(anchor(adr)).r
    val Adr2 = anchor(adr).r

    def trim(s: String): String = HTML.input(s).replace(" at ", "@")

    def unapply(s: String): Option[(String, String)] =
      s match {
        case Name1(a) => Some((trim(a), ""))
        case Name2(a) => Some((trim(a), ""))
        case Name_Adr1(a, b) => Some((trim(a), trim(b)))
        case Name_Adr2(a, b) => Some((trim(a), trim(b)))
        case Name_Adr3(a, b) => Some((trim(a), trim(b)))
        case Name_Adr4(a, b) => Some((trim(a), trim(b)))
        case Adr_Name1(b, a) => Some((trim(a), trim(b)))
        case Adr_Name2(b, a) => Some((trim(a), trim(b)))
        case Adr1(a) => Some(("", trim(a)))
        case Adr2(a) => Some(("", trim(a)))
        case _ => None
      }
  }

  object Date_Format
  {
    private val Trim1 = """\w+,\s*(.*)""".r
    private val Trim2 = """(.*?)\s*\(.*\)""".r
    private val Format =
      Date.Format(
        "d MMM uuuu H:m:s Z",
        "d MMM uuuu H:m:s z",
        "d MMM yy H:m:s Z",
        "d MMM yy H:m:s z")
    def unapply(s: String): Option[Date] =
    {
      val s0 = s.replaceAll("""\s+""", " ")
      val s1 =
         s0 match {
          case Trim1(s1) => s1
          case _ => s0
        }
      val s2 =
        s1 match {
          case Trim2(s2) => s2
          case _ => s1
        }
      Format.unapply(s2)
    }
  }


  /* mailing list archives */

  abstract class Archive(
    url: URL,
    name: String = "",
    tag: String = "")
  {
    def message_regex: Regex
    def message_content(href: String, lines: List[String]): Message

    private val main_url: URL =
      Url(Library.take_suffix[Char](_ == '/', Url.trim_index(url).toString.toList)._1.mkString + "/")

    private val main_html = Url.read(main_url)

    val list_name: String =
    {
      val title =
        """<title>The ([^</>]*) Archives</title>""".r.findFirstMatchIn(main_html).map(_.group(1))
      (proper_string(name) orElse title).getOrElse(error("Failed to determine mailing list name"))
    }
    override def toString: String = list_name

    def list_tag: String = proper_string(tag).getOrElse(list_name)

    def read_text(href: String): String = Url.read(new URL(main_url, href))

    def hrefs_text: List[String] =
      """href="([^"]+\.txt(?:\.gz)?)"""".r.findAllMatchIn(main_html).map(_.group(1)).toList

    def hrefs_msg: List[String] =
      (for {
        href <- """href="([^"]+)/date.html"""".r.findAllMatchIn(main_html).map(_.group(1))
        html = read_text(href + "/date.html")
        msg <- message_regex.findAllMatchIn(html).map(_.group(1))
      } yield href + "/" + msg).toList

    def get(target_dir: Path, href: String, progress: Progress = new Progress): Option[Path] =
    {
      val dir = target_dir + Path.basic(list_name)
      val path = dir + Path.explode(href)
      val url = new URL(main_url, href)
      val connection = url.openConnection
      try {
        val length = connection.getContentLengthLong
        val timestamp = connection.getLastModified
        val file = path.file
        if (file.isFile && file.length == length && file.lastModified == timestamp) None
        else {
          Isabelle_System.make_directory(path.dir)
          progress.echo("Getting " + url)
          val bytes =
            using(connection.getInputStream)(Bytes.read_stream(_, hint = length.toInt max 1024))
          Bytes.write(file, bytes)
          file.setLastModified(timestamp)
          Some(path)
        }
      }
      finally { connection.getInputStream.close() }
    }

    def download_text(target_dir: Path, progress: Progress = new Progress): List[Path] =
      hrefs_text.flatMap(get(target_dir, _, progress = progress))

    def download_msg(target_dir: Path, progress: Progress = new Progress): List[Path] =
      hrefs_msg.flatMap(get(target_dir, _, progress = progress))

    def download(target_dir: Path, progress: Progress = new Progress): List[Path] =
      download_text(target_dir, progress = progress) :::
      download_msg(target_dir, progress = progress)

    def trim_title(str: String): String =
    {
      val Trim1 = ("""\s*\Q[""" + list_tag + """]\E\s*(.*)""").r
      val Trim2 = """(?i:(?:re|fw|fwd)\s*:\s*)(.*)""".r
      val Trim3 = """\[\s*(.*?)\s*\]""".r
      @tailrec def trim(s: String): String =
        s match {
          case Trim1(s1) => trim(s1)
          case Trim2(s1) => trim(s1)
          case Trim3(s1) => trim(s1)
          case _ => s
        }
      trim(str)
    }

    def trim_name(str: String): String = str.replaceAll("""\s+""", " ")

    def get_messages(): List[Message] =
      for (href <- hrefs_msg) yield message_content(href, split_lines(read_text(href)))

    def find_messages(dir: Path): List[Message] =
    {
      for {
        file <- File.find_files(dir.file, file => file.getName.endsWith(".html"))
        rel_path <- File.relative_path(dir, File.path(file))
      } yield message_content(rel_path.implode, split_lines(File.read(file)))
    }
  }


  /* Isabelle mailing lists */

  object Isabelle_Users extends Archive(
    Url("https://lists.cam.ac.uk/pipermail/cl-isabelle-users"),
    name = "isabelle-users", tag = "isabelle")
  {
    override def message_regex: Regex = """<li><a name="\d+" href="(msg\d+\.html)">""".r

    private object Head extends
      Message_Chunk("<!--X-Head-of-Message-->", "<!--X-Head-of-Message-End-->")

    private object Body extends
      Message_Chunk("<!--X-Body-of-Message-->", "<!--X-Body-of-Message-End-->")

    override def trim_name(str: String): String =
    {
      val Trim = """(.*?)\s*via\s+Cl-isabelle-users""".r
      super.trim_name(str) match {
        case Trim(s) => s
        case s => s
      }
    }

    override def message_content(href: String, lines: List[String]): Message =
    {
      def err(msg: String = ""): Nothing =
        error("Malformed message: " + href + (if (msg.isEmpty) "" else "\n" + msg))

      val (head, body) =
        try { (Head.get(lines), Body.get(lines)) }
        catch { case ERROR(msg) => err(msg) }

      val date =
        message_match(head, """<li><em>Date</em>:\s*(.*?)\s*</li>""".r)
          .map(m => HTML.input(m.group(1))) match
        {
          case Some(Date_Format(d)) => d
          case Some(s) => err("Malformed Date: " + quote(s))
          case None => err("Missing Date")
        }

      val title =
        HTML.input(message_match(head, """<li><em>Subject</em>:\s*(.*)</li>""".r)
          .getOrElse(err("Missing Subject")).group(1))

      val (author_name, author_address) =
        message_match(head, """<li><em>From</em>:\s*(.*?)\s*</li>""".r) match {
          case None => err("Missing From")
          case Some(m) => Address.unapply(m.group(1)) getOrElse err("Malformed From")
        }

      Message(
        href, date, trim_title(title),
        trim_name(proper_string(author_name) getOrElse author_address),
        author_address,
        cat_lines(body))
    }
  }

  object Isabelle_Dev extends Archive(Url("https://mailmanbroy.in.tum.de/pipermail/isabelle-dev"))
  {
    override def message_regex: Regex = """<LI><A HREF="(\d+\.html)">""".r

    override def message_content(href: String, lines: List[String]): Message = ???
  }
}
