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
        case Command_Span(name, _) => if (name != "") name else "<command>"
        case Ignored_Span => "<ignored>"
        case Malformed_Span => "<malformed>"
      }
  }
  case class Command_Span(name: String, pos: Position.T) extends Kind
  case object Ignored_Span extends Kind
  case object Malformed_Span extends Kind

  sealed case class Span(kind: Kind, content: List[Token])
  {
    def length: Int = (0 /: content)(_ + _.source.length)

    def compact_source: (String, Span) =
    {
      val source: String =
        content match {
          case List(tok) => tok.source
          case toks => toks.map(_.source).mkString
        }

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
  }

  val empty: Span = Span(Ignored_Span, Nil)

  def unparsed(source: String): Span =
    Span(Malformed_Span, List(Token(Token.Kind.UNPARSED, source)))


  /* resolve inlined files */

  private def clean_tokens(tokens: List[Token]): List[(Token, Int)] =
  {
    def clean(toks: List[(Token, Int)]): List[(Token, Int)] =
      toks match {
        case (t1, i1) :: (t2, i2) :: rest =>
          if (t1.is_keyword && (t1.source == "%" || t1.source == "--")) clean(rest)
          else (t1, i1) :: clean((t2, i2) :: rest)
        case _ => toks
      }
    clean(tokens.zipWithIndex.filter({ case (t, _) => t.is_proper }))
  }

  private def find_file(tokens: List[(Token, Int)]): Option[(String, Int)] =
    tokens match {
      case (tok, _) :: toks =>
        if (tok.is_command)
          toks.collectFirst({ case (t, i) if t.is_name => (t.content, i) })
        else None
      case Nil => None
    }

  def span_files(syntax: Prover.Syntax, span: Span): (List[String], Int) =
    span.kind match {
      case Command_Span(name, _) =>
        syntax.load_command(name) match {
          case Some(exts) =>
            find_file(clean_tokens(span.content)) match {
              case Some((file, i)) =>
                if (exts.isEmpty) (List(file), i)
                else (exts.map(ext => file + "." + ext), i)
              case None => (Nil, -1)
            }
          case None => (Nil, -1)
        }
      case _ => (Nil, -1)
    }

  def resolve_files(
      resources: Resources,
      syntax: Prover.Syntax,
      node_name: Document.Node.Name,
      span: Span,
      get_blob: Document.Node.Name => Option[Document.Blob])
    : (List[Command.Blob], Int) =
  {
    val (files, index) = span_files(syntax, span)
    val blobs =
      files.map(file =>
        Exn.capture {
          val name =
            Document.Node.Name(resources.append(node_name.master_dir, Path.explode(file)))
          val blob = get_blob(name).map(blob => ((blob.bytes.sha1_digest, blob.chunk)))
          (name, blob)
        })
    (blobs, index)
  }
}
