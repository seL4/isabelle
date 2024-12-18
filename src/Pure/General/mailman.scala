/*  Title:      Pure/General/mailman.scala
    Author:     Makarius

Support for Mailman list servers, notably isabelle-users and isabelle-dev.
*/

package isabelle


import scala.annotation.tailrec
import scala.util.matching.Regex
import scala.util.matching.Regex.Match


object Mailman {
  /* mailing list messages */

  def is_address(s: String): Boolean =
    s.contains('@') && s.contains('.') && !s.contains(' ')

  private val standard_name: Map[String, String] =
    Map(
      "121171528:qq/com" -> "Guo Fan\n121171528:qq/com",
      "Aman Pohjola, Johannes (Data61, Kensington NSW)" -> "Johannes Aman Pohjola",
      "Andrei de AraÃjo Formiga" -> "Andrei de Araujo Formiga",
      "Benedikt/AHRENS:unice/fr" -> "Benedikt Ahrens\nBenedikt/AHRENS:unice/fr",
      "Berg, Nils Erik" -> "Nils Erik Berg",
      "Berger U/" -> "Ulrich Berger",
      "Bisping, Benjamin" -> "Benjamin Bisping",
      "Blanchette, J/C/" -> "Jasmin Christian Blanchette",
      "Buday Gergely István" -> "Gergely Buday",
      "CALaF1UJ9Uy0vGCu4WkBmbfuPDxG7nFm8hfeCMP+O3g7_5CQ0Bw:mail/gmail/com" -> "",
      "CRACIUN F/" -> "Florin Craciun",
      "Carsten Schuermann" -> "Carsten Schürmann",
      "Chris" -> "",
      "Christoph Lueth" -> "Christoph Lüth",
      "Claude Marche" -> "Claude Marché",
      "Daniel StÃwe" -> "Daniel Stüwe",
      "Daniel/Matichuk:data61/csiro/au" -> "Daniel Matichuk\nDaniel/Matichuk:data61/csiro/au",
      "Daniel/Matichuk:nicta/com/au" -> "Daniel Matichuk\nDaniel/Matichuk:nicta/com/au",
      "David MENTRE" -> "David MENTRÉ",
      "Dey, Katie" -> "Katie Dey",
      "Dr/ Brendan Patrick Mahony" -> "Brendan Mahony",
      "Farn" -> "Farn Wang",
      "Farquhar, Colin I" -> "Colin Farquhar",
      "Fernandez, Matthew" -> "Matthew Fernandez",
      "Filip Maric" -> "Filip Marić",
      "Filip MariÄ" -> "Filip Marić",
      "Fleury Mathias" -> "Mathias Fleury",
      "Francisco Jose CHAVES ALONSO" -> "Francisco Jose Chaves Alonso",
      "Frederic Tuong (Dr)" -> "Frederic Tuong",
      "Fulya" -> "Fulya Horozal",
      "George K/" -> "George Karabotsos",
      "Gidon Ernst" -> "Gidon ERNST",
      "Gransden, Thomas" -> "Thomas Gransden",
      "Hans-JÃrg Schurr" -> "Hans-Jörg Schurr",
      "Henri DEBRAT" -> "Henri Debrat",
      "Hitoshi Ohsaki (RTA publicity chair)" -> "Hitoshi Ohsaki",
      "Häuselmann Rafael" -> "Rafael Häuselmann",
      "Isabelle" -> "",
      "J/ Juhas (TUM)" -> "Jonatan Juhas",
      "Jackson, Vincent (Data61, Kensington NSW)" -> "Vincent Jackson",
      "Janney, Mark-P26816" -> "Mark Janney",
      "Jean François Molderez" -> "Jean-François Molderez",
      "Jean-Francois Molderez" -> "Jean-François Molderez",
      "John R Harrison" -> "John Harrison",
      "Jose DivasÃn" -> "Jose Divasón",
      "Julian" -> "",
      "Julien" -> "",
      "Klein, Gerwin (Data61, Kensington NSW)" -> "Gerwin Klein",
      "Kobayashi, Hidetsune" -> "Hidetsune Kobayashi",
      "Kylie Williams (IND)" -> "Kylie Williams",
      "Laarman, A/W/" -> "A/W/ Laarman",
      "Laurent Thery" -> "Laurent Théry",
      "Li, Chanjuan" -> "Li Chanjuan",
      "Lochbihler Andreas" -> "Andreas Lochbihler",
      "Luckhardt, Daniel" -> "Daniel Luckhardt",
      "Lutz Schroeder" -> "Lutz Schröder",
      "Lutz SchrÃder" -> "Lutz Schröder",
      "MACKENZIE Carlin" -> "Carlin MACKENZIE",
      "Makarius" -> "Makarius Wenzel",
      "Marco" -> "",
      "Mark" -> "",
      "Markus Mueller-Olm" -> "Markus Müller-Olm",
      "Markus" -> "",
      "Marmsoler, Diego" -> "Diego Marmsoler",
      "Martin Klebermass" -> "Martin Klebermaß",
      "Martyn Johnson via RT" -> "",
      "Mathias/Fleury:ens-rennes/fr" -> "Mathias Fleury\nmathias/fleury12:gmail/com",
      "Matthew" -> "",
      "Matthews, John R" -> "John Matthews",
      "McCarthy, Jim (C3ID)" -> "Jim McCarthy",
      "McCue, Brian" -> "Brian McCue",
      "Michael FÃrber" -> "Michael Färber",
      "Michel" -> "",
      "Miranda, Brando" -> "Brando Miranda",
      "Moscato, Mariano M/ \\(LARC-D320\\)\\[NATIONAL INSTITUTE OF AEROSPACE\\]" -> "Mariano M/ Moscato",
      "Mr Julian Fell" -> "Julian Fell",
      "Mueller Peter" -> "Peter Müller",
      "Munoz, Cesar Augusto (LARC-D320)" -> "Cesar A/ Munoz",
      "Nadel, Alexander" -> "Alexander Nadel",
      "Nagashima, Yutaka" -> "Yutaka Nagashima",
      "Norrish, Michael (Data61, Acton)" -> "Michael Norrish",
      "O'Leary, John W" -> "John W O'Leary",
      "Omar Montano Rivas" -> "Omar Montaño Rivas",
      "Omar MontaÃo Rivas" -> "Omar Montaño Rivas",
      "OndÅej KunÄar" -> "Ondřej Kunčar",
      "PALMER Jake" -> "Jake Palmer",
      "PAQUI LUCIO" -> "Paqui Lucio",
      "Pal, Abhik" -> "Abhik Pal",
      "Pasupuleti, Vijay" -> "Vijay Pasupuleti",
      "Peter Vincent Homeier" -> "Peter V/ Homeier",
      "Peter" -> "",
      "Philipp Ruemmer" -> "Philipp Rümmer",
      "Philipp RÃmmer" -> "Philipp Rümmer",
      "Piete Brooks via RT" -> "",
      "RTA publicity chair" -> "",
      "Raamsdonk, F/ van" -> "Femke van Raamsdonk",
      "Raul Gutierrez" -> "Raúl Gutiérrez",
      "RenÃ Thiemann" -> "René Thiemann",
      "Ridgway, John V/ E/" -> "John V/ E/ Ridgway",
      "Roggenbach M/" -> "Markus Roggenbach",
      "Rosu, Grigore" -> "Grigore Rosu",
      "Rozman, Mihaela" -> "Mihaela Rozman",
      "Schmaltz, J/" -> "Julien Schmaltz",
      "Serguei A/ Mokhov on behalf of PST-11" -> "Serguei A/ Mokhov",
      "Serguei Mokhov" -> "Serguei A/ Mokhov",
      "Shumeiko, Igor" -> "Igor Shumeiko",
      "Siek, Jeremy" -> "Jeremy Siek",
      "Silvio/Ranise:loria/fr" -> "Silvio Ranise\nSilvio/Ranise:loria/fr",
      "Siu, Tony" -> "Tony Siu",
      "Stüber, Sebastian" -> "Sebastian Stüber",
      "Thiemann, Rene" -> "René Thiemann",
      "Thiemann, René" -> "René Thiemann",
      "Thomas Arthur Leck Sewell" -> "Thomas Sewell",
      "Thomas Goethel" -> "Thomas Göthel",
      "Thomas/Sewell:data61/csiro/au" -> "Thomas Sewell\nThomas/Sewell:data61/csiro/au",
      "Tjark Weber via RT" -> "Tjark Weber",
      "Toby/Murray:data61/csiro/au" -> "Toby Murray\nToby/Murray:data61/csiro/au",
      "Urban, Christian" -> "Christian Urban",
      "Ursula Eschbach" -> "",
      "Van Staden Stephan" -> "Stephan van Staden",
      "Viktor Kuncak" -> "Viktor Kunčak",
      "Viorel Preoteasaa" -> "Viorel Preoteasa",
      "Wickerson, John P" -> "John Wickerson",
      "Wong, Yat" -> "Yat Wong",
      "YAMADA, Akihisa" -> "Akihisa Yamada",
      "YliÃs Falcone" -> "Yliès Falcone",
      "amir mohajeri" -> "Amir Mohajeri",
      "aniello murano" -> "Aniello Murano",
      "barzan stefania" -> "Stefania Barzan",
      "benhamou" -> "Belaid Benhamou",
      "charmi panchal" -> "Charmi Panchal",
      "chen kun" -> "Chen Kun",
      "chunhan wu" -> "Chunhan Wu",
      "daniel de la concepción sáez" -> "Daniel de la Concepción Sáez",
      "daniel/luckhardt:mathematik/uni-goettingen/de" -> "Logiker:gmx/net",
      "david streader" -> "David Streader",
      "eschbach:in/tum/de" -> "",
      "f/rabe:jacobs-university/de" -> "florian/rabe:fau/de",
      "florian:haftmann-online/de" -> "haftmann:in/tum/de",
      "fredegar:haftmann-online/de" -> "haftmann:in/tum/de",
      "gallais : ensl/org" -> "Guillaume Allais",
      "geng chen" -> "Geng Chen",
      "henning/seidler" -> "Henning Seidler",
      "hkb" -> "Hidetsune Kobayashi",
      "jobs-pm:inf/ethz/ch" -> "",
      "julien:RadboudUniversity" -> "",
      "jun sun" -> "Jun Sun",
      "jwang whu/edu/cn (jwang)" -> "jwang",
      "kostas pouliasis" -> "Kostas Pouliasis",
      "kristof/teichel:ptb/de" -> "Kristof Teichel\nkristof/teichel:ptb/de",
      "lucas cavalcante" -> "Lucas Cavalcante",
      "mahmoud abdelazim" -> "Mahmoud Abdelazim",
      "manish surolia" -> "Manish Surolia",
      "mantel" -> "Heiko Mantel",
      "marco caminati" -> "Marco Caminati",
      "mathias/fleury:ens-rennes/fr" -> "Mathias Fleury\nmathias/fleury12:gmail/com",
      "merz:loria/fr" -> "stephan/merz:loria/fr",
      "michel levy" -> "Michel Levy",
      "michel/levy2009:laposte/net" -> "Michel Levy\nmichel/levy2009:laposte/net",
      "nemouchi" -> "Yakoub Nemouchi",
      "noam neer" -> "Noam Neer",
      "olfa mraihi" -> "Olfa Mraihi",
      "pathsnottakenworkshop:gmail/com" -> "Leo Freitas\nleo/freitas:newcastle/ac/uk",
      "patrick barlatier" -> "Patrick Barlatier",
      "patrick dabou" -> "Patrick Dabou",
      "paul zimmermann" -> "Paul Zimmermann",
      "popescu2:illinois/edu" -> "Andrei Popescu",
      "recruiting" -> "",
      "recruiting:mais/informatik/tu-darmstadt/de" -> "",
      "roux cody" -> "Cody Roux",
      "scott constable" -> "Scott Constable",
      "superuser:mattweidner/com" -> "Matthew Weidner\nsuperuser:mattweidner/com",
      "urban:math/lmu/de" -> "Christian Urban\nurban:math/lmu/de",
      "veronique/cortier:loria/fr" -> "Veronique/Cortier:loria/fr",
      "vikram singh" -> "Vikram Singh",
      "wenzelm:in/tum/de" -> "makarius:sketis/net",
      "werner:lix/polytechnique/fr" -> "Benjamin Werner\nwerner:lix/polytechnique/fr",
      "wmansky:cs/princeton/edu" -> "William Mansky\nwmansky:cs/princeton/edu",
      "y/nemouchi:ensbiotech/edu/dz" -> "Yakoub Nemouchi\ny/nemouchi:ensbiotech/edu/dz",
      "ÐÑÐÐÐÑÐÐÐ ÐÐÐÐÐÐÐÑÐÐÐÑ ÐÐÐÑÐÐÐ" -> "",
      "∀X/Xπ - Tutorials about Proofs" -> "Bruno Woltzenlogel Paleo",
    )

  private def tune(s: String): String =
    s.replace(64.toChar, 58.toChar).replace(46.toChar, 47.toChar)

  private def untune(s: String): String =
    s.replace(58.toChar, 64.toChar).replace(47.toChar, 46.toChar)

  def standard_author_info(author_info: List[String]): List[String] =
    author_info.flatMap(s =>
      split_lines(standard_name.get(tune(s)).map(untune).getOrElse(s))).distinct

  sealed case class Message(
    name: String,
    date: Date,
    title: String,
    author_info: List[String],
    body: String,
    tags: List[String]
  ) {
    if (author_info.isEmpty || author_info.exists(_.isEmpty)) {
      error("Bad author information in " + quote(name))
    }

    override def toString: String = name
   }

  object Messages {
    type Graph = isabelle.Graph[String, Message]

    def apply(msgs: List[Message]): Messages = {
      def make_node(g: Graph, node: String, msg: Message): Graph =
        if (g.defined(node) && Date.Ordering.compare(g.get_node(node).date, msg.date) >= 0) g
        else g.default_node(node, msg)

      def connect_nodes(g: Graph, nodes: List[String]): Graph =
        nodes match {
          case Nil => g
          case a :: bs => bs.foldLeft(g)({ case (g1, b) => g1.add_edge(a, b).add_edge(b, a) })
        }

      new Messages(msgs.sortBy(_.date)(Date.Ordering),
        msgs.foldLeft[Graph](Graph.string)(
          { case (graph, msg) =>
              val nodes = msg.author_info
              connect_nodes(nodes.foldLeft(graph)(make_node(_, _, msg)), nodes)
          }))
    }

    def find(dir: Path): Messages = {
      val msgs =
        for {
          archive <- List(Isabelle_Users, Isabelle_Dev)
          msg <- archive.find_messages(dir + Path.basic(archive.list_name))
        } yield msg
      Messages(msgs)
    }

    sealed case class Cluster(author_info: List[String]) {
      val (addresses, names) = author_info.partition(is_address)

      val name: String =
        names.headOption getOrElse {
          addresses match {
            case a :: _ => a.substring(0, a.indexOf('@')).replace('.', ' ')
            case Nil => error("Empty cluster")
          }
        }

      val name_lowercase: String = Word.lowercase(name)

      def get_address: Option[String] = addresses.headOption

      def unique: Boolean = names.length == 1 && addresses.length == 1
      def multi: Boolean = names.length > 1 || addresses.length > 1

      def print: String = {
        val entries = names ::: (if (addresses.isEmpty) Nil else List("")) ::: addresses
        entries.mkString("\n  * ", "\n    ", "")
      }
    }
  }

  class Messages private(val sorted: List[Message], val graph: Messages.Graph) {
    override def toString: String = "Messages(" + sorted.size + ")"

    object Node_Ordering extends scala.math.Ordering[String] {
      override def compare(a: String, b: String): Int =
        Date.Rev_Ordering.compare(graph.get_node(a).date, graph.get_node(b).date)
    }

    def get_cluster(msg: Message): Messages.Cluster =
      Messages.Cluster(graph.all_succs(msg.author_info).sorted.sorted(Node_Ordering))

    def get_name(msg: Message): String = get_cluster(msg).name

    def get_address(msg: Message): String =
      get_cluster(msg).get_address getOrElse error("No author address for " + quote(msg.name))

    def check(check_all: Boolean, check_multi: Boolean = false): Unit = {
      val clusters = sorted.map(get_cluster).distinct.sortBy(_.name_lowercase)

      if (check_all) {
        Output.writeln(cat_lines("clusters:" :: clusters.map(_.print)))
      }
      else {
        val multi = if (check_multi) clusters.filter(_.multi) else Nil
        if (multi.nonEmpty) {
          Output.writeln(cat_lines("ambiguous clusters:" :: multi.map(_.print)))
        }
      }

      val unknown = clusters.filter(cluster => cluster.get_address.isEmpty)
      if (unknown.nonEmpty) {
        Output.writeln(cat_lines("\nunknown mail:" :: unknown.map(_.print)))
      }
    }
  }


  /* mailing list archives */

  abstract class Archive(
    url: Url,
    name: String = "",
    tag: String = ""
  ) {
    def message_regex: Regex
    def message_content(name: String, lines: List[String]): Message

    def message_match(lines: List[String], re: Regex): Option[Match] =
      lines.flatMap(re.findFirstMatchIn(_)).headOption

    def make_name(str: String): String = {
      val s =
        str.trim.replaceAll("""\s+""", " ").replaceAll(" at ", "@")
          .replace("mailbroy.informatik.tu-muenchen.de", "in.tum.de")
          .replace("informatik.tu-muenchen.de", "in.tum.de")
      if (s.startsWith("=") && s.endsWith("=")) "" else s
    }

    def make_body(lines: List[String]): String =
      cat_lines(Library.take_suffix[String](_.isEmpty, lines)._1)

    private val main_url: Url =
      Url(Library.take_suffix[Char](_ == '/', Url.trim_index(url).toString.toList)._1.mkString + "/")

    private val main_html = Url.read(main_url)

    val list_name: String = {
      val title =
        """<title>The ([^</>]*) Archives</title>""".r.findFirstMatchIn(main_html).map(_.group(1))
      (proper_string(name) orElse title).getOrElse(error("Failed to determine mailing list name"))
    }
    override def toString: String = list_name

    def full_name(href: String): String = list_name + "/" + href

    def list_tag: String = proper_string(tag).getOrElse(list_name)

    def read_text(href: String): String = Url.read(main_url.resolve(href))

    def hrefs_text: List[String] =
      """href="([^"]+\.txt(?:\.gz)?)"""".r.findAllMatchIn(main_html).map(_.group(1)).toList

    def hrefs_msg: List[String] =
      (for {
        href <- """href="([^"]+)/date.html"""".r.findAllMatchIn(main_html).map(_.group(1))
        html = read_text(href + "/date.html")
        msg <- message_regex.findAllMatchIn(html).map(_.group(1))
      } yield href + "/" + msg).toList

    def get(target_dir: Path, href: String, progress: Progress = new Progress): Option[Path] = {
      val dir = target_dir + Path.basic(list_name)
      val path = dir + Path.explode(href)
      val url = main_url.resolve(href)
      val connection = url.open_connection()
      try {
        val length = connection.getContentLengthLong
        val timestamp = connection.getLastModified
        if (path.is_file && File.size(path) == length && path.file.lastModified == timestamp) None
        else {
          Isabelle_System.make_directory(path.dir)
          progress.echo("Getting " + url)
          val bytes =
            using(connection.getInputStream)(Bytes.read_stream(_, hint = length.toInt max 1024))
          Bytes.write(path, bytes)
          path.file.setLastModified(timestamp)
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

    def make_title(str: String): String = {
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

    def find_messages(dir: Path): List[Message] = {
      for {
        file <- File.find_files(dir.file, file => File.is_html(file.getName))
        rel_path <- File.relative_path(dir, File.path(file))
      }
      yield {
        val name = full_name(rel_path.implode)
        message_content(name, split_lines(File.read(file)))
      }
    }
  }

  private class Message_Chunk(bg: String = "", en: String = "") {
    def unapply(lines: List[String]): Option[List[String]] = {
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
        error("Missing delimiters:" + if_proper(bg, " ") + bg + if_proper(en, " ") + en)
  }


  /* isabelle-users mailing list */

  object Isabelle_Users extends Archive(
    Url("https://lists.cam.ac.uk/pipermail/cl-isabelle-users"),
    name = "isabelle-users", tag = "isabelle"
  ) {
    override def message_regex: Regex = """<li><a name="\d+" href="(msg\d+\.html)">""".r

    private object Head extends
      Message_Chunk(bg = "<!--X-Head-of-Message-->", en = "<!--X-Head-of-Message-End-->")

    private object Body extends
      Message_Chunk(bg = "<!--X-Body-of-Message-->", en = "<!--X-Body-of-Message-End-->")

    private object Date_Format {
      private val Trim1 = """\w+,\s*(.*)""".r
      private val Trim2 = """(.*?)\s*\(.*\)""".r
      private val Format =
        Date.Format(
          "d MMM uuuu H:m:s Z",
          "d MMM uuuu H:m:s z",
          "d MMM yy H:m:s Z",
          "d MMM yy H:m:s z")
      def unapply(s: String): Option[Date] = {
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

    override def make_name(str: String): String = {
      val s = Library.perhaps_unsuffix(" via Cl-isabelle-users", super.make_name(str))
      if (s == "cl-isabelle-users@lists.cam.ac.uk") "" else s
    }

    object Address {
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

      def parse(s: String): List[String] =
        s match {
          case Name1(a) => List(a)
          case Name2(a) => List(a)
          case Name_Adr1(a, b) => List(a, b)
          case Name_Adr2(a, b) => List(a, b)
          case Name_Adr3(a, b) => List(a, b)
          case Name_Adr4(a, b) => List(a, b)
          case Adr_Name1(b, a) => List(a, b)
          case Adr_Name2(b, a) => List(a, b)
          case Adr1(a) => List(a)
          case Adr2(a) => List(a)
          case _ => Nil
        }
    }

    override def message_content(name: String, lines: List[String]): Message = {
      def err(msg: String = ""): Nothing =
        error("Malformed message: " + name + if_proper(msg, "\n" + msg))

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

      def parse_author_info(re: Regex): List[String] =
        message_match(head, re) match {
          case None => Nil
          case Some(m) => Address.parse(m.group(1)).map(a => HTML.input(make_name(a)))
        }

      val author_info =
        (parse_author_info("""<li><em>From</em>:\s*(.*?)\s*</li>""".r) :::
          parse_author_info("""<li><em>Reply-to</em>:\s*(.*?)\s*</li>""".r))
        .distinct.filter(_.nonEmpty)

      if (author_info.isEmpty) err("Malformed author information")

      val tags = List(list_name)

      Message(name, date, title, standard_author_info(author_info), body, tags)
    }
  }


  /* isabelle-dev mailing list */

  object Isabelle_Dev extends Archive(Url("https://mailmanbroy.in.tum.de/pipermail/isabelle-dev")) {
    override def message_regex: Regex = """<LI><A HREF="(\d+\.html)">""".r

    private object Head extends Message_Chunk(en = "<!--beginarticle-->")
    private object Body extends Message_Chunk(bg = "<!--beginarticle-->", en = "<!--endarticle-->")

    private object Date_Format {
      val Format = Date.Format("E MMM d H:m:s z uuuu")
      def unapply(s: String): Option[Date] = Format.unapply(s.replaceAll("""\s+""", " "))
    }

    override def message_content(name: String, lines: List[String]): Message = {
      def err(msg: String = ""): Nothing =
        error("Malformed message: " + name + if_proper(msg, "\n" + msg))

      val (head, body) =
        try { (Head.get(lines), make_body(Body.get(lines))) }
        catch { case ERROR(msg) => err(msg) }

      val date =
        message_match(head, """\s*<I>(.*)</I>""".r).map(m => HTML.input(m.group(1))) match {
          case Some(Date_Format(d)) => d
          case Some(s) => err("Malformed Date: " + quote(s))
          case None => err("Missing Date")
        }

      val (title, author_address) = {
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

      val author_info = List(author_name, author_address)
      val tags = List(list_name)

      Message(name, date, title, standard_author_info(author_info), body, tags)
    }
  }
}
