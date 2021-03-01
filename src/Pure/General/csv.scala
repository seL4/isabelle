/*  Title:      Pure/General/csv.scala
    Author:     Makarius

Support for CSV: RFC 4180.
*/

package isabelle


object CSV
{
  def print_field(field: Any): String =
  {
    val str = field.toString
    if (str.exists("\",\r\n".contains(_))) {
      (for (c <- str) yield { if (c == '"') "\"\"" else c.toString }).mkString("\"", "", "\"")
    }
    else str
  }

  sealed case class Record(fields: Any*)
  {
    override def toString: String = fields.iterator.map(print_field).mkString(",")
  }

  sealed case class File(name: String, header: List[String], records: List[Record])
  {
    override def toString: String = (Record(header:_*) :: records).mkString("\r\n")

    def file_name: String = name + ".csv"
    def write(dir: Path): Unit = isabelle.File.write(dir + Path.explode(file_name), toString)
  }
}
