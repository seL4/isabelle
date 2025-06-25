/*  Title:      Pure/Tools/doc.scala
    Author:     Makarius

Access to Isabelle examples and documentation.
*/

package isabelle


import scala.collection.mutable


object Doc {
  /* entries */

  case class Section(title: String, important: Boolean, entries: List[Entry])
  case class Entry(name: String, path: Path, title: String = "") {
    def view(): Unit = Doc.view(path)
    override def toString: String =  // GUI label
      if (title.nonEmpty) {
        val style = GUI.Style_HTML
        style.enclose(style.make_bold(name) + style.make_text(": " + title))
      }
      else name
  }

  def plain_file(path0: Path,
    env: Isabelle_System.Settings = Isabelle_System.Settings()
  ): Option[Entry] = {
    val path1 = path0.expand_env(env)
    if (path1.is_file && !path1.is_pdf) {
      val a = path0.implode
      val b = Library.try_unprefix("$ISABELLE_HOME/", a).getOrElse(a)
      Some(Entry(b, path1))
    }
    else None
  }


  /* contents */

  def dirs(): List[Path] =
    Path.split(Isabelle_System.getenv("ISABELLE_DOCS"))

  private def contents_lines(): List[(Path, String)] =
    for {
      dir <- dirs()
      catalog = dir + Path.basic("Contents")
      if catalog.is_file
      line <- Library.trim_split_lines(File.read(catalog))
    } yield (dir, line)

  object Contents {
    def apply(sections: List[Section]): Contents = new Contents(sections)

    def section(title: String, important: Boolean, entries: List[Entry]): Contents =
      apply(List(Section(title, important, entries)))
  }
  class Contents private(val sections: List[Section]) {
    def ++ (other: Contents): Contents = new Contents(sections ::: other.sections)
    def entries(name: String => Boolean = _ => true, pdf: Boolean = false): List[Entry] =
      sections.flatMap(s => s.entries.filter(e => name(e.name) && (!pdf || e.path.is_pdf)))
  }

  def release_notes(): Contents =
    Contents.section("Release Notes", true,
      Path.split(Isabelle_System.getenv_strict("ISABELLE_DOCS_RELEASE_NOTES"))
        .flatMap(plain_file(_)))

  def examples(ml_settings: ML_Settings): Contents = {
    val env = Isabelle_System.Settings(putenv = List(ml_settings.ml_sources_root))
    Contents.section("Examples", true,
      Path.split(Isabelle_System.getenv_strict("ISABELLE_DOCS_EXAMPLES")).map(file =>
        plain_file(file, env = env) match {
          case Some(entry) => entry
          case None => error("Bad entry in ISABELLE_DOCS_EXAMPLES: " + file)
        }))
  }

  def main_contents(): Contents = {
    val result = new mutable.ListBuffer[Section]
    val entries = new mutable.ListBuffer[Entry]
    var section: Option[Section] = None

    def flush(): Unit =
      if (section.nonEmpty) {
        result += section.get.copy(entries = entries.toList)
        entries.clear()
        section = None
      }

    def begin(s: Section): Unit = {
      flush()
      section = Some(s)
    }

    val Section_ = """^(\S.*)\s*$""".r
    val Entry_ = """^\s+(\S+)\s+(.+)\s*$""".r

    for ((dir, line) <- contents_lines()) {
      line match {
        case Section_(text) =>
          Library.try_unsuffix("!", text) match {
            case None => begin(Section(text, false, Nil))
            case Some(txt) => begin(Section(txt, true, Nil))
          }
        case Entry_(name, title) =>
          val path = dir + Path.basic(name)
          entries += Entry(name, if (path.is_file) path else path.pdf, title = title)
        case _ =>
      }
    }

    flush()
    Contents(result.toList)
  }

  def contents(ml_settings: ML_Settings): Contents = {
    examples(ml_settings) ++ release_notes() ++ main_contents()
  }

  object Doc_Names extends Scala.Fun_String("doc_names") {
    val here = Scala_Project.here
    def apply(arg: String): String = {
      val ml_settings = ML_Settings.system(Options.init() + ("ML_platform=" + arg))
      cat_lines((for (entry <- contents(ml_settings).entries(pdf = true)) yield entry.name).sorted)
    }
  }


  /* view */

  def view(path: Path): Unit = {
    if (!path.is_file) error("Bad Isabelle documentation file: " + path)
    else if (path.is_pdf) Isabelle_System.pdf_viewer(path)
    else Output.writeln(Library.trim_line(File.read(path)), stdout = true)
  }


  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("doc", "view Isabelle documentation",
    Scala_Project.here,
    { args =>
      val getopts = Getopts("""
Usage: isabelle doc [DOC ...]

  View Isabelle documentation.
""")
      val docs = getopts(args)

      val ml_settings = ML_Settings.system(Options.init())

      if (docs.isEmpty) Output.writeln(cat_lines(contents_lines().map(_._2)), stdout = true)
      else {
        docs.foreach(name =>
          contents(ml_settings).entries(name = docs.contains).headOption match {
            case Some(entry) => entry.view()
            case None => error("No Isabelle documentation entry: " + quote(name))
          }
        )
      }
    })
}
