/*  Title:      Pure/ML/ml_root.scala
    Author:     Makarius

Support for ML project ROOT file, with imitation of ML "use" commands.
*/

package isabelle


object ML_Root
{
  /* parser */

  val USE = "use"
  val USE_DEBUG = "use_debug"
  val USE_NO_DEBUG = "use_no_debug"
  val USE_THY = "use_thy"

  lazy val syntax =
    Outer_Syntax.init() + ";" +
      (USE, Some((Keyword.THY_LOAD, Nil)), None) +
      (USE_DEBUG, Some((Keyword.THY_LOAD, Nil)), None) +
      (USE_NO_DEBUG, Some((Keyword.THY_LOAD, Nil)), None) +
      (USE_THY, Some((Keyword.THY_LOAD, List("thy"))), None)

  private object Parser extends Parse.Parser
  {
    val entry: Parser[Path] =
      command(USE_THY) ~! string ^^
        { case _ ~ a => Resources.thy_path(Path.explode(a)) } |
      (command(USE) | command(USE_DEBUG) | command(USE_NO_DEBUG)) ~! string ^^
        { case _ ~ a => Path.explode(a) }

    val entries: Parser[List[Path]] =
      rep(entry <~ $$$(";"))
  }

  def read_files(root: Path): List[Path] =
  {
    val toks = Token.explode(syntax.keywords, File.read(root))
    val start = Token.Pos.file(root.implode)

    Parser.parse_all(Parser.entries, Token.reader(toks, start)) match {
      case Parser.Success(entries, _) => entries
      case bad => error(bad.toString)
    }
  }
}
