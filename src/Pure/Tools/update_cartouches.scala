/*  Title:      Pure/Tools/update_cartouches.scala
    Author:     Makarius

Update theory syntax to use cartouches.
*/

package isabelle


object Update_Cartouches
{
  /* update cartouches */

  private def cartouche(s: String): String =
    Symbol.open + s + Symbol.close

  private val Verbatim_Body = """(?s)[ \t]*(.*?)[ \t]*""".r

  val Text_Antiq = """(?s)@\{\s*text\b\s*(.+)\}""".r

  def update_text(content: String): String =
  {
    (try { Some(Antiquote.read(content)) } catch { case ERROR(_) => None }) match {
      case Some(ants) =>
        val ants1: List[Antiquote.Antiquote] =
          ants.map(ant =>
            ant match {
              case Antiquote.Antiq(Text_Antiq(body)) =>
                Token.explode(Keyword.Keywords.empty, body).filterNot(_.is_space) match {
                  case List(tok) => Antiquote.Control(cartouche(tok.content))
                  case _ => ant
                }
              case _ => ant
            })
        if (ants == ants1) content else ants1.map(_.source).mkString
      case None => content
    }
  }

  def update_cartouches(replace_text: Boolean, path: Path)
  {
    val text0 = File.read(path)

    // outer syntax cartouches
    val text1 =
      (for (tok <- Token.explode(Keyword.Keywords.empty, text0).iterator)
        yield {
          if (tok.kind == Token.Kind.ALT_STRING) cartouche(tok.content)
          else if (tok.kind == Token.Kind.VERBATIM) {
            tok.content match {
              case Verbatim_Body(s) => cartouche(s)
              case s => tok.source
            }
          }
          else tok.source
        }
      ).mkString

    // cartouches within presumed text tokens
    val text2 =
      if (replace_text) {
        (for (tok <- Token.explode(Keyword.Keywords.empty, text1).iterator)
          yield {
            if (tok.kind == Token.Kind.STRING || tok.kind == Token.Kind.CARTOUCHE) {
              val content = tok.content
              val content1 = update_text(content)

              if (content == content1) tok.source
              else if (tok.kind == Token.Kind.STRING) Outer_Syntax.quote_string(content1)
              else cartouche(content1)
            }
            else tok.source
          }).mkString
      }
      else text1

    if (text0 != text2) {
      Output.writeln("changing " + path)
      File.write_backup2(path, text2)
    }
  }


  /* command line entry point */

  def main(args: Array[String])
  {
    Command_Line.tool0 {
      args.toList match {
        case Properties.Value.Boolean(replace_text) :: files =>
          files.foreach(file => update_cartouches(replace_text, Path.explode(file)))
        case _ => error("Bad arguments:\n" + cat_lines(args))
      }
    }
  }
}
