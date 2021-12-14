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
    override def toString: String = name
    def print: String =
      name + "\n" + date + "\n" + title + "\n" +
      quote(author_name) + "\n" + "<" + author_address + ">\n"

    def normal_address: String = Word.lowercase(author_address)
  }

  object Messages
  {
    def apply(msgs: List[Message]): Messages =
      new Messages(msgs.sortBy(_.date)(Date.Ordering))
  }

  class Messages private(val sorted: List[Message])
  {
    override def toString: String = "Messages(" + sorted.length + ")"

    def check(): Unit =
    {
      val proper = sorted.filter(msg => msg.author_name.nonEmpty && msg.author_address.nonEmpty)
      val address_name = Multi_Map.from(proper.map(msg => (msg.normal_address, msg.author_name)))
      val name_address = Multi_Map.from(proper.map(msg => (msg.author_name, msg.normal_address)))

      def print_dup(a: String, bs: List[String]): String =
        "  * " + a + bs.mkString("\n      ", "\n      ", "")

      def print_dups(title: String, m: Multi_Map[String, String]): Unit =
      {
        val dups = m.iterator_list.filter(p => p._2.length > 1).toList
        if (dups.nonEmpty) {
          Output.writeln(cat_lines(title :: dups.map(p => print_dup(p._1, p._2))))
        }
      }

      print_dups("\nduplicate names:", address_name)
      print_dups("\nduplicate addresses:", name_address)

      def get_name(msg: Message): Option[String] =
        proper_string(msg.author_name) orElse address_name.get(msg.author_address)

      val missing_name =
        sorted.flatMap(msg =>
          if (get_name(msg).isEmpty) Some(proper_string(msg.author_address).getOrElse(msg.name))
          else None).toSet.toList.sorted

      val missing_address =
        sorted.flatMap(msg =>
          if (msg.author_address.isEmpty) Some(proper_string(msg.author_name).getOrElse(msg.name))
          else None).toSet.toList.sorted

      if (missing_name.nonEmpty) {
        Output.writeln(("missing name:" :: missing_name).mkString("\n", "\n  ", ""))
      }

      if (missing_address.nonEmpty) {
        Output.writeln(("missing address:" :: missing_address).mkString("\n", "\n  ", ""))
      }
    }
  }


  /* mailing list archives */

  abstract class Archive(
    url: URL,
    name: String = "",
    tag: String = "")
  {
    def message_regex: Regex
    def message_content(name: String, lines: List[String]): Message

    def message_match(lines: List[String], re: Regex): Option[Match] =
      lines.flatMap(re.findFirstMatchIn(_)).headOption

    def make_name(str: String): String =
      str.replaceAll("""\s+""", " ").replaceAll(" at ", "@")

    def make_body(lines: List[String]): String =
      cat_lines(Library.take_suffix[String](_.isEmpty, lines)._1)

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

    def full_name(href: String): String = list_name + "/" + href

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

    def make_title(str: String): String =
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

    def get_messages(): List[Message] =
      for (href <- hrefs_msg) yield message_content(href, split_lines(read_text(href)))

    def find_messages(dir: Path): List[Message] =
    {
      for {
        file <- File.find_files(dir.file, file => file.getName.endsWith(".html"))
        rel_path <- File.relative_path(dir, File.path(file))
      }
      yield {
        val name = full_name(rel_path.implode)
        message_content(name, split_lines(File.read(file)))
      }
    }
  }

  private class Message_Chunk(bg: String = "", en: String = "")
  {
    def unapply(lines: List[String]): Option[List[String]] =
    {
      val res1 =
        if (bg.isEmpty) Some(lines)
        else {
          lines.dropWhile(_ != bg) match {
            case Nil => None
            case _ :: rest => Some(rest)
          }
        }
      if (en.isEmpty) res1
      else {
        res1 match {
          case None => None
          case Some(lines1) =>
            val lines2 = lines1.takeWhile(_ != en)
            if (lines1.drop(lines2.length).isEmpty) None else Some(lines2)
        }
      }
    }

    def get(lines: List[String]): List[String] =
      unapply(lines) getOrElse
        error("Missing delimiters:" +
          (if (bg.nonEmpty) " " else "") + bg +
          (if (en.nonEmpty) " " else "") + en)
  }


  /* isabelle-users mailing list */

  object Isabelle_Users extends Archive(
    Url("https://lists.cam.ac.uk/pipermail/cl-isabelle-users"),
    name = "isabelle-users", tag = "isabelle")
  {
    override def message_regex: Regex = """<li><a name="\d+" href="(msg\d+\.html)">""".r

    private object Head extends
      Message_Chunk(bg = "<!--X-Head-of-Message-->", en = "<!--X-Head-of-Message-End-->")

    private object Body extends
      Message_Chunk(bg = "<!--X-Body-of-Message-->", en = "<!--X-Body-of-Message-End-->")

    private object Date_Format
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

    override def make_name(str: String): String =
    {
      val s = Library.perhaps_unsuffix("via Cl-isabelle-users", super.make_name(str))
      if (s == "cl-isabelle-users@lists.cam.ac.uk") "" else s
    }

    object Address
    {
      private def anchor(s: String): String = """<a href="[^"]*">""" + s + """</a>"""
      private def angl(s: String): String = """&lt;""" + s + """&gt;"""
      private def quot(s: String): String = """&quot;""" + s + """&quot;"""
      private def paren(s: String): String = """\(""" + s + """\)"""
      private val adr = """([^<>]*? at [^<>]*?)"""
      private val any = """([^<>]*?)"""
      private val spc = """\s*"""

      private val Name1 = quot(anchor(any)).r
      private val Name2 = quot(any).r
      private val Name_Adr1 = (quot(anchor(any)) + spc + angl(anchor(adr))).r
      private val Name_Adr2 = (quot(any) + spc + angl(anchor(adr))).r
      private val Name_Adr3 = (anchor(any) + spc + angl(anchor(adr))).r
      private val Name_Adr4 = (any + spc + angl(anchor(adr))).r
      private val Adr_Name1 = (angl(anchor(adr)) + spc + paren(any)).r
      private val Adr_Name2 = (anchor(adr) + spc + paren(any)).r
      private val Adr1 = angl(anchor(adr)).r
      private val Adr2 = anchor(adr).r

      def unapply(s: String): Option[(String, String)] =
        s match {
          case Name1(a) => Some((make_name(a), ""))
          case Name2(a) => Some((make_name(a), ""))
          case Name_Adr1(a, b) => Some((make_name(a), make_name(b)))
          case Name_Adr2(a, b) => Some((make_name(a), make_name(b)))
          case Name_Adr3(a, b) => Some((make_name(a), make_name(b)))
          case Name_Adr4(a, b) => Some((make_name(a), make_name(b)))
          case Adr_Name1(b, a) => Some((make_name(a), make_name(b)))
          case Adr_Name2(b, a) => Some((make_name(a), make_name(b)))
          case Adr1(a) => Some(("", make_name(a)))
          case Adr2(a) => Some(("", make_name(a)))
          case _ => None
        }
    }

    override def message_content(name: String, lines: List[String]): Message =
    {
      def err(msg: String = ""): Nothing =
        error("Malformed message: " + name + (if (msg.isEmpty) "" else "\n" + msg))

      val (head, body) =
        try { (Head.get(lines), make_body(Body.get(lines))) }
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
        make_title(
          HTML.input(message_match(head, """<li><em>Subject</em>:\s*(.*)</li>""".r)
            .getOrElse(err("Missing Subject")).group(1)))

      val (author_name, author_address) =
        message_match(head, """<li><em>From</em>:\s*(.*?)\s*</li>""".r) match {
          case None => err("Missing From")
          case Some(m) =>
            val (a0, b0) = Address.unapply(m.group(1)) getOrElse err("Malformed From")
            val a = HTML.input(a0)
            val b = HTML.input(b0)
            (if (a == b) "" else a, b)
        }

      Message(name, date, title, author_name, author_address, body)
    }
  }


  /* isabelle-dev mailing list */

  object Isabelle_Dev extends Archive(Url("https://mailmanbroy.in.tum.de/pipermail/isabelle-dev"))
  {
    override def message_regex: Regex = """<LI><A HREF="(\d+\.html)">""".r

    private object Head extends Message_Chunk(en = "<!--beginarticle-->")
    private object Body extends Message_Chunk(bg = "<!--beginarticle-->", en = "<!--endarticle-->")

    private object Date_Format
    {
      val Format = Date.Format("E MMM d H:m:s z uuuu")
      def unapply(s: String): Option[Date] = Format.unapply(s.replaceAll("""\s+""", " "))
    }

    override def make_name(str: String): String =
    {
      val s = Library.perhaps_unsuffix("via RT", super.make_name(str))
      if (s == "sys-admin@cl.cam.ac.uk") "" else s
    }

    override def message_content(name: String, lines: List[String]): Message =
    {
      def err(msg: String = ""): Nothing =
        error("Malformed message: " + name + (if (msg.isEmpty) "" else "\n" + msg))

      val (head, body) =
        try { (Head.get(lines), make_body(Body.get(lines))) }
        catch { case ERROR(msg) => err(msg) }

      val date =
        message_match(head, """\s*<I>(.*)</I>""".r).map(m => HTML.input(m.group(1))) match {
          case Some(Date_Format(d)) => d
          case Some(s) => err("Malformed Date: " + quote(s))
          case None => err("Missing Date")
        }

      val (title, author_address) =
      {
        message_match(head, """TITLE="([^"]+)">(.*)""".r) match {
          case Some(m) => (make_title(HTML.input(m.group(1))), make_name(HTML.input(m.group(2))))
          case None => err("Missing TITLE")
        }
      }

      val author_name =
        message_match(head, """\s*<B>(.*)</B>""".r) match {
          case None => err("Missing author")
          case Some(m) =>
            val a = make_name(HTML.input(m.group(1)))
            if (a == author_address) "" else a
        }

      Message(name, date, title, author_name, author_address, body)
    }
  }
}
