/*  Title:      Pure/ML/ml_statistics.ML
    Author:     Makarius

ML runtime statistics.
*/

package isabelle


object ML_Statistics
{
  /* read properties from build log */

  private val line_prefix = "\fML_statistics = "

  private val syntax = Outer_Syntax.empty + "," + "(" + ")" + "[" + "]"

  private object Parser extends Parse.Parser
  {
    private def stat: Parser[(String, String)] =
      keyword("(") ~ string ~ keyword(",") ~ string ~ keyword(")") ^^
      { case _ ~ x ~ _ ~ y ~ _ => (x, y) }
    private def stats: Parser[Properties.T] =
      keyword("[") ~> repsep(stat, keyword(",")) <~ keyword("]")

    def parse_stats(s: String): Properties.T =
    {
      parse_all(stats, Token.reader(syntax.scan(s))) match {
        case Success(result, _) => result
        case bad => error(bad.toString)
      }
    }
  }

  def read_log(log: Path): List[Properties.T] =
    for {
      line <- split_lines(File.read_gzip(log))
      if line.startsWith(line_prefix)
      stats = line.substring(line_prefix.length)
    } yield Parser.parse_stats(stats)
}
