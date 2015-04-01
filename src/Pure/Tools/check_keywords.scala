/*  Title:      Pure/Tools/check_keywords.scala
    Author:     Makarius

Check theory sources for conflicts with proposed keywords.
*/

package isabelle


object Check_Keywords
{
  def conflicts(
    keywords: Keyword.Keywords,
    check: Set[String],
    input: CharSequence,
    start: Token.Pos): List[(Token, Position.T)] =
  {
    object Parser extends Parse.Parser
    {
      private val conflict =
        position(token("token", tok => !(tok.is_command || tok.is_keyword) && check(tok.source)))
      private val other = token("token", _ => true)
      private val item = conflict ^^ (x => Some(x)) | other ^^ (_ => None)

      val result =
        parse_all(rep(item), Token.reader(Token.explode(keywords, input), start)) match {
          case Success(res, _) => for (Some(x) <- res) yield x
          case bad => error(bad.toString)
        }
    }
    Parser.result
  }

  def conflicts(
    keywords: Keyword.Keywords, check: Set[String], path: Path): List[(Token, Position.T)] =
    conflicts(keywords, check, File.read(path), Token.Pos.file(path.expand.implode))
}
