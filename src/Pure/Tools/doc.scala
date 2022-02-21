/*  Title:      Pure/Tools/doc.scala
    Author:     Makarius

Access to Isabelle documentation.
*/

package isabelle


import scala.collection.mutable


object Doc
{
  /* dirs */

  def dirs(): List[Path] =
    Path.split(Isabelle_System.getenv("ISABELLE_DOCS"))


  /* contents */

  private def contents_lines(): List[(Path, String)] =
    for {
      dir <- dirs()
      catalog = dir + Path.basic("Contents")
      if catalog.is_file
      line <- Library.trim_split_lines(File.read(catalog))
    } yield (dir, line)

  case class Section(title: String, important: Boolean, entries: List[Entry])
  sealed abstract class Entry
  case class Doc(name: String, title: String, path: Path) extends Entry
  case class Text_File(name: String, path: Path) extends Entry

  def text_file(path: Path): Option[Text_File] =
    if (path.is_file) {
      val a = path.implode
      val b = Library.try_unprefix("$ISABELLE_HOME/", a).getOrElse(a)
      Some(Text_File(b, path))
    }
    else None

  def release_notes(): Section =
    Section("Release Notes", true,
      Path.split(Isabelle_System.getenv_strict("ISABELLE_DOCS_RELEASE_NOTES")).flatMap(text_file))

  def examples(): Section =
    Section("Examples", true,
      Path.split(Isabelle_System.getenv_strict("ISABELLE_DOCS_EXAMPLES")).map(file =>
        text_file(file) match {
          case Some(entry) => entry
          case None => error("Bad entry in ISABELLE_DOCS_EXAMPLES: " + file)
        }))

  def main_contents(): List[Section] =
  {
    val result = new mutable.ListBuffer[Section]
    val entries = new mutable.ListBuffer[Entry]
    var section: Option[Section] = None

    def flush(): Unit =
      if (section.nonEmpty) {
        result += section.get.copy(entries = entries.toList)
        entries.clear()
        section = None
      }

    def begin(s: Section): Unit =
    {
      flush()
      section = Some(s)
    }

    val Section_ = """^(\S.*)\s*$""".r
    val Doc_ = """^\s+(\S+)\s+(.+)\s*$""".r

    for ((dir, line) <- contents_lines()) {
      line match {
        case Section_(text) =>
          Library.try_unsuffix("!", text) match {
            case None => begin(Section(text, false, Nil))
            case Some(txt) => begin(Section(txt, true, Nil))
          }
        case Doc_(name, title) =>
          entries += Doc(name, title, dir + Path.basic(name))
        case _ =>
      }
    }

    flush()
    result.toList
  }

  def contents(): List[Section] =
  {
    examples() :: release_notes() :: main_contents()
  }

  def doc_entries(sections: List[Section]): List[Doc] =
    sections.flatMap(_.entries).collect({ case doc: Doc => doc })

  object Doc_Names extends Scala.Fun_String("doc_names")
  {
    val here = Scala_Project.here
    def apply(arg: String): String =
      if (arg.nonEmpty) error("Bad argument: " + quote(arg))
      else cat_lines((for (doc <- doc_entries(contents())) yield doc.name).sorted)
  }


  /* view */

  def view(path: Path): Unit =
  {
    if (path.is_file) Output.writeln(Library.trim_line(File.read(path)), stdout = true)
    else {
      val pdf = path.ext("pdf")
      if (pdf.is_file) Isabelle_System.pdf_viewer(pdf)
      else error("Bad Isabelle documentation file: " + pdf)
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("doc", "view Isabelle documentation",
    Scala_Project.here, args =>
  {
    val getopts = Getopts("""
Usage: isabelle doc [DOC ...]

  View Isabelle documentation.
""")
    val docs = getopts(args)

    val sections = contents()
    if (docs.isEmpty) Output.writeln(cat_lines(contents_lines().map(_._2)), stdout = true)
    else {
      docs.foreach(name =>
        doc_entries(sections).find(_.name == name) match {
          case Some(doc) => view(doc.path)
          case None => error("No Isabelle documentation entry: " + quote(name))
        }
      )
    }
  })
}
