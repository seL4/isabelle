/*  Title:      Pure/General/latex.scala
    Author:     Makarius

Support for LaTeX.
*/

package isabelle


import java.io.{File => JFile}

import scala.annotation.tailrec
import scala.collection.mutable
import scala.collection.immutable.TreeMap
import scala.util.matching.Regex


object Latex {
  /* output name for LaTeX macros */

  private val output_name_map: Map[Char, String] =
    Map('_' -> "UNDERSCORE",
      '\'' -> "PRIME",
      '0' -> "ZERO",
      '1' -> "ONE",
      '2' -> "TWO",
      '3' -> "THREE",
      '4' -> "FOUR",
      '5' -> "FIVE",
      '6' -> "SIX",
      '7' -> "SEVEN",
      '8' -> "EIGHT",
      '9' -> "NINE")

  def output_name(name: String): String =
    if (name.exists(output_name_map.keySet)) {
      Library.string_builder() { res =>
        for (c <- name) {
          output_name_map.get(c) match {
            case None => res += c
            case Some(s) => res ++= s
          }
        }
      }
    }
    else name


  /* index entries */

  def index_escape(str: String): String = {
    val special1 = "!\"@|"
    val special2 = "\\{}#"
    if (str.exists(c => special1.contains(c) || special2.contains(c))) {
      Library.string_builder() { res =>
        for (c <- str) {
          if (special1.contains(c)) {
            res ++= "\\char"
            res ++= Value.Int(c)
          }
          else {
            if (special2.contains(c)) { res += '"'}
            res += c
          }
        }
      }
    }
    else str
  }

  object Index_Item {
    sealed case class Value(text: Text, like: String)
    def unapply(tree: XML.Tree): Option[Value] =
      tree match {
        case XML.Wrapped_Elem(Markup.Latex_Index_Item(_), text, like) =>
          Some(Value(text, XML.content(like)))
        case _ => None
      }
  }

  object Index_Entry {
    sealed case class Value(items: List[Index_Item.Value], kind: String)
    def unapply(tree: XML.Tree): Option[Value] =
      tree match {
        case XML.Elem(Markup.Latex_Index_Entry(kind), body) =>
          val items = body.map(Index_Item.unapply)
          if (items.forall(_.isDefined)) Some(Value(items.map(_.get), kind)) else None
        case _ => None
      }
  }


  /* tags */

  object Tags {
    enum Op { case fold, drop, keep }

    val standard = "document,theory,proof,ML,visible,-invisible,important,unimportant"

    private def explode(spec: String): List[String] = space_explode(',', spec)

    def apply(spec: String): Tags =
      new Tags(spec,
        (explode(standard) ::: explode(spec)).foldLeft(TreeMap.empty[String, Op]) {
          case (m, tag) =>
            tag.toList match {
              case '/' :: cs => m + (cs.mkString -> Op.fold)
              case '-' :: cs => m + (cs.mkString -> Op.drop)
              case '+' :: cs => m + (cs.mkString -> Op.keep)
              case cs => m + (cs.mkString -> Op.keep)
            }
        })

    val empty: Tags = apply("")
  }

  class Tags private(spec: String, map: TreeMap[String, Tags.Op]) {
    override def toString: String = spec

    def get(name: String): Option[Tags.Op] = map.get(name)

    def sty(comment_latex: Boolean): File.Content = {
      val path = Path.explode("isabelletags.sty")
      val comment =
        if (comment_latex) """\usepackage{comment}"""
        else """%plain TeX version of comment package -- much faster!
\let\isafmtname\fmtname\def\fmtname{plain}
\usepackage{comment}
\let\fmtname\isafmtname"""
      val tags =
        (for ((name, op) <- map.iterator)
          yield "\\isa" + op + "tag{" + name + "}").toList
      File.content(path, comment + """

\newcommand{\isakeeptag}[1]%
{\includecomment{isadelim#1}\includecomment{isatag#1}\csarg\def{isafold#1}{}}
\newcommand{\isadroptag}[1]%
{\excludecomment{isadelim#1}\excludecomment{isatag#1}\csarg\def{isafold#1}{}}
\newcommand{\isafoldtag}[1]%
{\includecomment{isadelim#1}\excludecomment{isatag#1}\csarg\def{isafold#1}{\isafold{#1}}}

""" + terminate_lines(tags))
    }
  }


  /* output text and positions */

  type Text = XML.Body

  def position(a: String, b: String): String = "%:%" + a + "=" + b + "%:%\n"

  def init_position(file_pos: String): List[String] =
    if (file_pos.isEmpty) Nil
    else List("\\endinput\n", position(Markup.FILE, file_pos))

  def append_position(path: Path, file_pos: String): Unit = {
    val pos = init_position(file_pos).mkString
    if (pos.nonEmpty) {
      val sep = if (File.read(path).endsWith("\n")) "" else "\n"
      File.append(path, sep + pos)
    }
  }

  def copy_file(src: Path, dst: Path): Unit = {
    Isabelle_System.copy_file(src, dst)
    if (src.is_latex) {
      val target = if (dst.is_dir) dst + src.base else dst
      val file_pos = File.symbolic_path(src)
      append_position(target, file_pos)
    }
  }

  def copy_file_base(base_dir: Path, src: Path, target_dir: Path): Unit = {
    Isabelle_System.copy_file_base(base_dir, src, target_dir)
    if (src.is_latex) {
      val file_pos = File.symbolic_path(base_dir + src)
      append_position(target_dir + src, file_pos)
    }
  }

  class Output(val options: Options) {
    def latex_output(latex_text: Text): String = make(latex_text)

    def latex_macro0(name: String, optional_argument: String = ""): Text =
      XML.string("\\" + name + optional_argument)

    def latex_macro(name: String, body: Text, optional_argument: String = ""): Text =
      XML.enclose("\\" + name + optional_argument + "{", "}", body)

    def latex_environment(name: String, body: Text, optional_argument: String = ""): Text =
      XML.enclose(
        "%\n\\begin{" + name + "}" + optional_argument + "%\n",
        "%\n\\end{" + name + "}", body)

    def latex_heading(kind: String, body: Text, optional_argument: String = ""): Text =
      XML.enclose(
        "%\n\\" + options.string("document_heading_prefix") + kind + optional_argument + "{",
        "%\n}\n", body)

    def latex_body(kind: String, body: Text, optional_argument: String = ""): Text =
      latex_environment("isamarkup" + kind, body, optional_argument)

    def latex_tag(name: String, body: Text, delim: Boolean = false): Text = {
      val s = output_name(name)
      val kind = if (delim) "delim" else "tag"
      val end = if (delim) "" else "{\\isafold" + s + "}%\n"
      if (options.bool("document_comment_latex")) {
        XML.enclose(
          "%\n\\begin{isa" + kind + s + "}\n",
          "%\n\\end{isa" + kind + s + "}\n" + end, body)
      }
      else {
        XML.enclose(
          "%\n\\isa" + kind + s + "\n",
          "%\n\\endisa" + kind + s + "\n" + end, body)
      }
    }

    def cite(inner: Bibtex.Cite.Inner): Text = {
      val body =
        latex_macro0(inner.kind) :::
        (if (inner.location.isEmpty) Nil
         else XML.string("[") ::: inner.location ::: XML.string("]")) :::
        XML.string("{" + inner.citations + "}")

      if (inner.pos.isEmpty) body
      else List(XML.Elem(Markup.Latex_Output(inner.pos), body))
    }

    def index_item(item: Index_Item.Value): String = {
      val like = if_proper(item.like, index_escape(item.like) + "@")
      val text = index_escape(latex_output(item.text))
      like + text
    }

    def index_entry(entry: Index_Entry.Value): Text = {
      val items = entry.items.map(index_item).mkString("!")
      val kind = if_proper(entry.kind, "|" + index_escape(entry.kind))
      latex_macro("index", XML.string(items + kind))
    }


    /* standard output of text with per-line positions */

    def unknown_elem(elem: XML.Elem, pos: Position.T): XML.Body =
      error("Unknown latex markup element " + quote(elem.name) + Position.here(pos) +
        ":\n" + XML.string_of_tree(elem))

    def make(
      latex_text: Text,
      file_pos: String = "",
      line_pos: Properties.T => Option[Int] = Position.Line.unapply
    ): String = {
      var line = 1
      val result = new mutable.ListBuffer[String]
      val positions = mutable.ListBuffer.from(init_position(file_pos))

      val file_position = if (file_pos.isEmpty) Position.none else Position.File(file_pos)

      def traverse(xml: XML.Body): Unit = {
        xml.foreach {
          case XML.Text(s) =>
            line += Library.count_newlines(s)
            result += s
          case elem @ XML.Elem(markup, body) =>
            val a = Markup.Optional_Argument.get(markup.properties)
            traverse {
              markup match {
                case Markup.Document_Latex(props) =>
                  if (positions.nonEmpty) {
                    for (l <- line_pos(props)) {
                      val s = position(Value.Int(line), Value.Int(l))
                      if (positions.last != s) positions += s
                    }
                  }
                  body
                case Markup.Latex_Output(_) => XML.string(latex_output(body))
                case Markup.Latex_Macro0(name) if body.isEmpty => latex_macro0(name, a)
                case Markup.Latex_Macro(name) => latex_macro(name, body, a)
                case Markup.Latex_Environment(name) => latex_environment(name, body, a)
                case Markup.Latex_Heading(kind) => latex_heading(kind, body, a)
                case Markup.Latex_Body(kind) => latex_body(kind, body, a)
                case Markup.Latex_Delim(name) => latex_tag(name, body, delim = true)
                case Markup.Latex_Tag(name) => latex_tag(name, body)
                case Markup.Latex_Cite(_) =>
                  elem match {
                    case Bibtex.Cite(inner) => cite(inner)
                    case _ => unknown_elem(elem, file_position)
                  }
                case Markup.Latex_Index_Entry(_) =>
                  elem match {
                    case Index_Entry(entry) => index_entry(entry)
                    case _ => unknown_elem(elem, file_position)
                  }
                case _ => unknown_elem(elem, file_position)
              }
            }
        }
      }
      traverse(latex_text)

      result ++= positions
      result.mkString
    }
  }


  /* generated .tex file */

  private val File_Pattern = """^%:%file=(.+)%:%$""".r
  private val Line_Pattern = """^*%:%(\d+)=(\d+)%:%$""".r

  def read_tex_file(tex_file: Path): Tex_File = {
    val positions =
      Line.logical_lines(File.read(tex_file)).reverse.
        takeWhile(_ != "\\endinput").reverse

    val source_file =
      positions match {
        case File_Pattern(file) :: _ => Some(file)
        case _ => None
      }

    val source_lines =
      if (source_file.isEmpty) Nil
      else
        positions.flatMap(line =>
          line match {
            case Line_Pattern(Value.Int(line), Value.Int(source_line)) => Some(line -> source_line)
            case _ => None
          })

    new Tex_File(tex_file, source_file, source_lines)
  }

  final class Tex_File private[Latex](
    tex_file: Path,
    source_file: Option[String],
    source_lines: List[(Int, Int)]
  ) {
    override def toString: String = tex_file.toString

    def source_position(l: Int): Option[Position.T] =
      source_file match {
        case None => None
        case Some(file) =>
          val source_line =
            source_lines.iterator.takeWhile({ case (m, _) => m <= l }).
              foldLeft(0) { case (_, (_, n)) => n }
          if (source_line == 0) None else Some(Position.Line_File(source_line, file))
      }

    def position(line: Int): Position.T =
      source_position(line) getOrElse
        Position.Line_File(line, source_file.getOrElse(tex_file.implode))
  }


  /* latex log */

  def latex_errors(dir: Path, root_name: String): List[String] = {
    val root_log_path = dir + Path.explode(root_name).log
    if (root_log_path.is_file) {
      for { (msg, pos) <- filter_errors(dir, File.read(root_log_path)) }
        yield "Latex error" + Position.here(pos) + ":\n" + Library.indent_lines(2, msg)
    }
    else Nil
  }

  def filter_errors(dir: Path, root_log: String): List[(String, Position.T)] = {
    val seen_files = Synchronized(Map.empty[JFile, Tex_File])

    def check_tex_file(path: Path): Option[Tex_File] =
      seen_files.change_result(seen =>
        seen.get(path.file) match {
          case None =>
            if (path.is_file) {
              val tex_file = read_tex_file(path)
              (Some(tex_file), seen + (path.file -> tex_file))
            }
            else (None, seen)
          case some => (some, seen)
        })

    def tex_file_position(path: Path, line: Int): Position.T =
      check_tex_file(path) match {
        case Some(tex_file) => tex_file.position(line)
        case None => Position.Line_File(line, path.implode)
      }

    object File_Line_Error {
      val Pattern: Regex = """^(.*?\.\w\w\w):(\d+): (.*)$""".r
      def unapply(line: String): Option[(Path, Int, String)] =
        line match {
          case Pattern(file, Value.Int(line), message) =>
            val path = File.standard_path(file)
            if (Path.is_wellformed(path)) {
              val file = (dir + Path.explode(path)).canonical
              val msg = Library.perhaps_unprefix("LaTeX Error: ", message)
              if (file.is_file) Some((file, line, msg)) else None
            }
            else None
          case _ => None
        }
    }

    val Line_Error = """^l\.\d+ (.*)$""".r
    val More_Error =
      List(
        "<argument>",
        "<template>",
        "<recently read>",
        "<to be read again>",
        "<inserted text>",
        "<output>",
        "<everypar>",
        "<everymath>",
        "<everydisplay>",
        "<everyhbox>",
        "<everyvbox>",
        "<everyjob>",
        "<everycr>",
        "<mark>",
        "<everyeof>",
        "<write>").mkString("^(?:", "|", ") (.*)$").r

    val Bad_Font = """^LaTeX Font Warning: (Font .*\btxmia\b.* undefined).*$""".r
    val Bad_File = """^! LaTeX Error: (File `.*' not found\.)$""".r

    val error_ignore =
      Set(
        "See the LaTeX manual or LaTeX Companion for explanation.",
        "Type  H <return>  for immediate help.")

    def error_suffix1(lines: List[String]): Option[String] = {
      val lines1 =
        lines.take(20).takeWhile({ case File_Line_Error((_, _, _)) => false case _ => true })
      lines1.zipWithIndex.collectFirst({
        case (Line_Error(msg), i) =>
          cat_lines(lines1.take(i).filterNot(error_ignore) ::: List(msg)) })
    }
    def error_suffix2(lines: List[String]): Option[String] =
      lines match {
        case More_Error(msg) :: _ => Some(msg)
        case _ => None
      }

    @tailrec def filter(
      lines: List[String],
      result: List[(String, Position.T)]
    ) : List[(String, Position.T)] = {
      lines match {
        case File_Line_Error((file, line, msg1)) :: rest1 =>
          val pos = tex_file_position(file, line)
          val msg2 = error_suffix1(rest1) orElse error_suffix2(rest1) getOrElse ""
          filter(rest1, (Exn.cat_message(msg1, msg2), pos) :: result)
        case Bad_Font(msg) :: rest =>
          filter(rest, (msg, Position.none) :: result)
        case Bad_File(msg) :: rest =>
          filter(rest, (msg, Position.none) :: result)
        case _ :: rest => filter(rest, result)
        case Nil => result.reverse
      }
    }

    filter(Line.logical_lines(root_log), Nil)
  }
}
