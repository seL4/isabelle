/*  Title:      Pure/PIDE/command_span.scala
    Author:     Makarius

Syntactic representation of command spans.
*/

package isabelle


import scala.collection.mutable
import scala.util.parsing.input.CharSequenceReader


object Command_Span {
  /* loaded files */

  object Loaded_Files {
    val none: Loaded_Files = Loaded_Files(Nil, -1)
  }
  sealed case class Loaded_Files(files: List[String], index: Int)

  abstract class Load_Command(val name: String, val here: Scala_Project.Here)
  extends Isabelle_System.Service {
    override def toString: String = print("")

    def print(body: String): String =
      if (body.nonEmpty) "Load_Command(" + body + ")"
      else if (name.nonEmpty) print("name = " + quote(name))
      else "Load_Command"

    def print_extensions: String =
      print("name = " + quote(name) + ", extensions = " + commas_quote(extensions))

    def position: Position.T = here.position

    def extensions: List[String] = Nil

    def loaded_files(tokens: List[(Token, Int)]): Loaded_Files =
      tokens.collectFirst({ case (t, i) if t.is_embedded => (t.content, i) }) match {
        case Some((file, i)) =>
          extensions match {
            case Nil => Loaded_Files(List(file), i)
            case exts => Loaded_Files(exts.map(ext => file + "." + ext), i)
          }
        case None => Loaded_Files.none
      }
  }

  object Load_Default extends Load_Command("", Scala_Project.here)

  lazy val load_commands: List[Load_Command] =
    Load_Default :: Isabelle_System.make_services(classOf[Load_Command])


  /* span kind */

  sealed abstract class Kind {
    def keyword_kind: Option[String] = None

    override def toString: String =
      this match {
        case command: Command_Span => proper_string(command.name) getOrElse "<command>"
        case Ignored_Span => "<ignored>"
        case Malformed_Span => "<malformed>"
        case Theory_Span => "<theory>"
      }
  }
  case class Command_Span(override val keyword_kind: Option[String], name: String, pos: Position.T)
    extends Kind
  case object Ignored_Span extends Kind
  case object Malformed_Span extends Kind
  case object Theory_Span extends Kind


  /* span */

  sealed case class Span(kind: Kind, content: List[Token]) {
    def is_theory: Boolean = kind == Theory_Span

    def name: String =
      kind match { case k: Command_Span => k.name case _ => "" }

    def position: Position.T =
      kind match { case k: Command_Span => k.pos case _ => Position.none }

    def keyword_pos(start: Token.Pos): Token.Pos =
      kind match {
        case _: Command_Span =>
          content.iterator.takeWhile(tok => !tok.is_command).foldLeft(start)(_.advance(_))
        case _ => start
      }

    def is_keyword_kind(pred: String => Boolean, other: Boolean = false): Boolean =
      kind.keyword_kind match {
        case Some(k) => pred(k)
        case None => other
      }

    def is_begin: Boolean = content.exists(_.is_begin)
    def is_end: Boolean = content.exists(_.is_end)

    def content_reader: CharSequenceReader = Scan.char_reader(Token.implode(content))

    def length: Int = content.foldLeft(0)(_ + _.source.length)
    def symbol_length: Symbol.Offset = content.foldLeft(0)(_ + _.symbol_length)

    def compact_source: (String, Span) = {
      val source = Token.implode(content)
      val content1 = new mutable.ListBuffer[Token]
      var i = 0
      for (Token(kind, s) <- content) {
        val n = s.length
        val s1 = source.substring(i, i + n)
        content1 += Token(kind, s1)
        i += n
      }
      (source, Span(kind, content1.toList))
    }

    def clean_arguments: List[(Token, Int)] = {
      if (name.nonEmpty) {
        def clean(toks: List[(Token, Int)]): List[(Token, Int)] =
          toks match {
            case (t1, i1) :: (t2, i2) :: rest =>
              if (t1.is_keyword && t1.source == "%" && t2.is_name) clean(rest)
              else (t1, i1) :: clean((t2, i2) :: rest)
            case _ => toks
          }
        clean(content.zipWithIndex.filter({ case (t, _) => t.is_proper }))
          .dropWhile({ case (t, _) => !t.is_command })
          .dropWhile({ case (t, _) => t.is_command })
      }
      else Nil
    }

    def is_load_command(syntax: Outer_Syntax): Boolean =
      syntax.load_command(name).isDefined

    def loaded_files(syntax: Outer_Syntax): Loaded_Files =
      syntax.load_command(name) match {
        case None => Loaded_Files.none
        case Some(a) =>
          load_commands.find(_.name == a) match {
            case Some(load_command) => load_command.loaded_files(clean_arguments)
            case None => error("Undefined load command function: " + a)
          }
      }
  }

  val empty: Span = Span(Ignored_Span, Nil)

  def unparsed(source: String, theory: Boolean = false): Span = {
    val kind = if (theory) Theory_Span else Malformed_Span
    Span(kind, List(Token(Token.Kind.UNPARSED, source)))
  }
}
