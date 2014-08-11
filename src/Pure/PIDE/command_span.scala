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
        case Command_Span(name) => if (name != "") name else "<command>"
        case Ignored_Span => "<ignored>"
        case Malformed_Span => "<malformed>"
      }
  }
  case class Command_Span(name: String) extends Kind
  case object Ignored_Span extends Kind
  case object Malformed_Span extends Kind

  sealed case class Span(kind: Kind, content: List[Token])
  {
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

  private def find_file(tokens: List[Token]): Option[String] =
  {
    def clean(toks: List[Token]): List[Token] =
      toks match {
        case t :: _ :: ts if t.is_keyword && (t.source == "%" || t.source == "--") => clean(ts)
        case t :: ts => t :: clean(ts)
        case Nil => Nil
      }
    clean(tokens.filter(_.is_proper)) match {
      case tok :: toks if tok.is_command => toks.find(_.is_name).map(_.content)
      case _ => None
    }
  }

  def span_files(syntax: Prover.Syntax, span: Span): List[String] =
    span.kind match {
      case Command_Span(name) =>
        syntax.load_command(name) match {
          case Some(exts) =>
            find_file(span.content) match {
              case Some(file) =>
                if (exts.isEmpty) List(file)
                else exts.map(ext => file + "." + ext)
              case None => Nil
            }
          case None => Nil
        }
      case _ => Nil
    }

  def resolve_files(
      resources: Resources,
      syntax: Prover.Syntax,
      node_name: Document.Node.Name,
      span: Span,
      get_blob: Document.Node.Name => Option[Document.Blob])
    : List[Command.Blob] =
  {
    span_files(syntax, span).map(file_name =>
      Exn.capture {
        val name =
          Document.Node.Name(resources.append(node_name.master_dir, Path.explode(file_name)))
        val blob = get_blob(name).map(blob => ((blob.bytes.sha1_digest, blob.chunk)))
        (name, blob)
      })
  }
}

