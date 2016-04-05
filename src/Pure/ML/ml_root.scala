/*  Title:      Pure/ML/ml_root.scala
    Author:     Makarius

Support for ML project ROOT file, with imitation of ML "use" commands.
*/

package isabelle


object ML_Root
{
  /* parser */

  val ROOT_ML = Path.explode("ROOT.ML")

  val USE = "use"
  val USE_DEBUG = "use_debug"
  val USE_NO_DEBUG = "use_no_debug"
  val USE_THY = "use_thy"

  lazy val syntax =
    Outer_Syntax.init() + ";" +
      (USE, Some((Keyword.THY_LOAD, Nil)), None) +
      (USE_DEBUG, Some((Keyword.THY_LOAD, Nil)), None) +
      (USE_NO_DEBUG, Some((Keyword.THY_LOAD, Nil)), None) +
      (USE_THY, Some((Keyword.THY_LOAD, Nil)), None)

  private object Parser extends Parse.Parser
  {
    val entry: Parser[(String, String)] =
      (command(USE) | command(USE_DEBUG) | command(USE_NO_DEBUG) | command(USE_THY)) ~!
        (string ~ $$$(";")) ^^ { case a ~ (b ~ _) => (a, b) }

    def parse(in: Token.Reader): ParseResult[List[(String, String)]] =
      parse_all(rep(entry), in)
  }

  def read(dir: Path): List[(String, Path)] =
  {
    val root = dir + ROOT_ML

    val toks = Token.explode(syntax.keywords, File.read(root))
    val start = Token.Pos.file(root.implode)

    Parser.parse(Token.reader(toks, start)) match {
      case Parser.Success(entries, _) =>
        for ((a, b) <- entries) yield {
          val path = dir + Path.explode(b)
          (a, if (a == USE_THY) Resources.thy_path(path) else path)
        }
      case bad => error(bad.toString)
    }
  }
}
