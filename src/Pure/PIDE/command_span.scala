/*  Title:      Pure/PIDE/command_span.scala
    Author:     Makarius

Syntactic representation of command spans.
*/

package isabelle


import scala.collection.mutable


object Command_Span
{
  sealed abstract class Kind {
    override def toString: String =
      this match {
        case Command_Span(name, _) => proper_string(name) getOrElse "<command>"
        case Ignored_Span => "<ignored>"
        case Malformed_Span => "<malformed>"
        case Theory_Span => "<theory>"
      }
  }
  case class Command_Span(name: String, pos: Position.T) extends Kind
  case object Ignored_Span extends Kind
  case object Malformed_Span extends Kind
  case object Theory_Span extends Kind

  sealed case class Span(kind: Kind, content: List[Token])
  {
    def is_theory: Boolean = kind == Theory_Span

    def name: String =
      kind match { case Command_Span(name, _) => name case _ => "" }

    def position: Position.T =
      kind match { case Command_Span(_, pos) => pos case _ => Position.none }

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

    def loaded_files(syntax: Outer_Syntax): (List[String], Int) =
      syntax.load_command(name) match {
        case Some(exts) =>
          find_file(clean_tokens(content)) match {
            case Some((file, i)) =>
              if (exts.isEmpty) (List(file), i)
              else (exts.map(ext => file + "." + ext), i)
            case None => (Nil, -1)
          }
        case None => (Nil, -1)
      }
  }

  val empty: Span = Span(Ignored_Span, Nil)

  def unparsed(source: String, theory: Boolean): Span =
  {
    val kind = if (theory) Theory_Span else Malformed_Span
    Span(kind, List(Token(Token.Kind.UNPARSED, source)))
  }


  /* loaded files */

  def clean_tokens(tokens: List[Token]): List[(Token, Int)] =
  {
    def clean(toks: List[(Token, Int)]): List[(Token, Int)] =
      toks match {
        case (t1, i1) :: (t2, i2) :: rest =>
          if (t1.is_keyword && t1.source == "%" && t2.is_name) clean(rest)
          else (t1, i1) :: clean((t2, i2) :: rest)
        case _ => toks
      }
    clean(tokens.zipWithIndex.filter({ case (t, _) => t.is_proper }))
  }

  def find_file(tokens: List[(Token, Int)]): Option[(String, Int)] =
    if (tokens.exists({ case (t, _) => t.is_command })) {
      tokens.dropWhile({ case (t, _) => !t.is_command }).
        collectFirst({ case (t, i) if t.is_embedded => (t.content, i) })
    }
    else None


  /* XML data representation */

  def encode: XML.Encode.T[Span] = (span: Span) =>
  {
    import XML.Encode._
    val kind: T[Kind] =
      variant(List(
        { case Command_Span(a, b) => (List(a), properties(b)) },
        { case Ignored_Span => (Nil, Nil) },
        { case Malformed_Span => (Nil, Nil) }))
    pair(kind, list(Token.encode))((span.kind, span.content))
  }

  def decode: XML.Decode.T[Span] = (body: XML.Body) =>
  {
    import XML.Decode._
    val kind: T[Kind] =
      variant(List(
        { case (List(a), b) => Command_Span(a, properties(b)) },
        { case (Nil, Nil) => Ignored_Span },
        { case (Nil, Nil) => Malformed_Span }))
    val (k, toks) = pair(kind, list(Token.decode))(body)
    Span(k, toks)
  }
}
