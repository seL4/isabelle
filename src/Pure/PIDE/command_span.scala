/*  Title:      Pure/PIDE/command_span.scala
    Author:     Makarius

Syntactic representation of command spans.
*/

package isabelle


import scala.collection.mutable


object Command_Span
{
  /* loaded files */

  object Loaded_Files
  {
    val none: Loaded_Files = Loaded_Files(Nil, -1)
  }
  sealed case class Loaded_Files(files: List[String], index: Int)

  class Load_Command(val name: String) extends Isabelle_System.Service
  {
    override def toString: String = name

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

  lazy val load_commands: List[Load_Command] =
    new Load_Command("") :: Isabelle_System.make_services(classOf[Load_Command])


  /* span kind */

  sealed abstract class Kind {
    override def toString: String =
      this match {
        case Command_Span(name, _, _) => proper_string(name) getOrElse "<command>"
        case Ignored_Span => "<ignored>"
        case Malformed_Span => "<malformed>"
        case Theory_Span => "<theory>"
      }
  }
  case class Command_Span(name: String, pos: Position.T, abs_pos: Position.T) extends Kind
  case object Ignored_Span extends Kind
  case object Malformed_Span extends Kind
  case object Theory_Span extends Kind


  /* span */

  sealed case class Span(kind: Kind, content: List[Token])
  {
    def is_theory: Boolean = kind == Theory_Span

    def name: String =
      kind match { case k: Command_Span => k.name case _ => "" }

    def position: Position.T =
      kind match { case k: Command_Span => k.pos case _ => Position.none }

    def absolute_position: Position.T =
      kind match { case k: Command_Span => k.abs_pos case _ => Position.none }

    def keyword_pos(start: Token.Pos): Token.Pos =
      kind match {
        case _: Command_Span =>
          (start /: content.iterator.takeWhile(tok => !tok.is_command))(_.advance(_))
        case _ => start
      }

    def is_kind(keywords: Keyword.Keywords, pred: String => Boolean, other: Boolean): Boolean =
      keywords.kinds.get(name) match {
        case Some(k) => pred(k)
        case None => other
      }

    def is_begin: Boolean = content.exists(_.is_begin)
    def is_end: Boolean = content.exists(_.is_end)

    def length: Int = (0 /: content)(_ + _.source.length)

    def compact_source: (String, Span) =
    {
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

    def clean_arguments: List[(Token, Int)] =
    {
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

  def unparsed(source: String, theory: Boolean): Span =
  {
    val kind = if (theory) Theory_Span else Malformed_Span
    Span(kind, List(Token(Token.Kind.UNPARSED, source)))
  }
}
