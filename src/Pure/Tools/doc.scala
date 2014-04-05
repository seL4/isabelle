/*  Title:      Pure/Tools/doc.scala
    Author:     Makarius

View Isabelle documentation.
*/

package isabelle


import scala.util.matching.Regex


object Doc
{
  /* dirs */

  def dirs(): List[Path] =
    Path.split(Isabelle_System.getenv("ISABELLE_DOCS")).map(dir =>
      if (dir.is_dir) dir
      else error("Bad documentation directory: " + dir))


  /* contents */

  private def contents_lines(): List[(Path, String)] =
    for {
      dir <- dirs()
      catalog = dir + Path.basic("Contents")
      if catalog.is_file
      line <- split_lines(Library.trim_line(File.read(catalog)))
    } yield (dir, line)

  sealed abstract class Entry
  case class Section(text: String) extends Entry
  case class Doc(name: String, title: String, path: Path) extends Entry
  case class Text_File(name: String, path: Path) extends Entry

  def text_file(name: String): Option[Text_File] =
  {
    val path = Path.variable("ISABELLE_HOME") + Path.explode(name)
    if (path.is_file) Some(Text_File(name, path))
    else None
  }

  private val Section_Entry = new Regex("""^(\S.*)\s*$""")
  private val Doc_Entry = new Regex("""^\s+(\S+)\s+(.+)\s*$""")

  private def release_notes(): List[Entry] =
  {
    val names =
      List("ANNOUNCE", "README", "NEWS", "COPYRIGHT", "CONTRIBUTORS",
        "contrib/README", "README_REPOSITORY")
    Section("Release notes") ::
      (for (name <- names; entry <- text_file(name)) yield entry)
  }

  private def examples(): List[Entry] =
  {
    val names =
      List(
        "src/HOL/ex/Seq.thy",
        "src/HOL/ex/ML.thy",
        "src/HOL/Unix/Unix.thy",
        "src/HOL/Isar_Examples/Drinker.thy",
        "src/Tools/SML/Examples.thy")
    Section("Examples") :: names.map(name => text_file(name).get)
  }

  def contents(): List[Entry] =
    (for {
      (dir, line) <- contents_lines()
      entry <-
        line match {
          case Section_Entry(text) => Some(Section(text))
          case Doc_Entry(name, title) => Some(Doc(name, title, dir + Path.basic(name)))
          case _ => None
        }
    } yield entry) ::: release_notes() ::: examples()


  /* view */

  def view(path: Path)
  {
    if (path.is_file) Console.println(File.read(path))
    else {
      val pdf = path.ext("pdf")
      if (pdf.is_file) Isabelle_System.pdf_viewer(pdf)
      else error("Bad Isabelle documentation file: " + pdf)
    }
  }


  /* command line entry point */

  def main(args: Array[String])
  {
    Command_Line.tool {
      if (args.isEmpty) Console.println(cat_lines(contents_lines().map(_._2)))
      else {
        val entries = contents()
        args.foreach(arg =>
          entries.collectFirst { case Doc(name, _, path) if arg == name => path } match {
            case Some(path) => view(path)
            case None => error("No Isabelle documentation entry: " + quote(arg))
          }
        )
      }
      0
    }
  }
}

