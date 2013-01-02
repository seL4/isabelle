/*  Title:      Pure/ML/ml_statistics.ML
    Author:     Makarius

ML runtime statistics.
*/

package isabelle


import scala.collection.immutable.{SortedSet, SortedMap}


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


  /* content interpretation */

  val Now = new Properties.Double("now")
  final case class Entry(time: Double, data: Map[String, Double])

  def apply(stats: List[Properties.T]): ML_Statistics = new ML_Statistics(stats)
  def apply(log: Path): ML_Statistics = apply(read_log(log))
}

final class ML_Statistics private(val stats: List[Properties.T])
{
  require(!stats.isEmpty && stats.forall(props => ML_Statistics.Now.unapply(props).isDefined))

  val time_start = ML_Statistics.Now.unapply(stats.head).get
  val duration = ML_Statistics.Now.unapply(stats.last).get - time_start

  val names: Set[String] =
    SortedSet.empty[String] ++
      (for (props <- stats.iterator; (x, _) <- props.iterator if x != ML_Statistics.Now.name)
        yield x)

  val content: List[ML_Statistics.Entry] =
    stats.map(props => {
      val time = ML_Statistics.Now.unapply(props).get - time_start
      require(time >= 0.0)
      val data =
        SortedMap.empty[String, Double] ++
          (for ((x, y) <- props.iterator if x != ML_Statistics.Now.name)
            yield (x, java.lang.Double.parseDouble(y)))
      ML_Statistics.Entry(time, data)
    })
}

