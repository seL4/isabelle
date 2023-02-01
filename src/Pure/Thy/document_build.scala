/*  Title:      Pure/Thy/document_build.scala
    Author:     Makarius

Build theory document (PDF) from session database.
*/

package isabelle


object Document_Build {
  /* document variants */

  abstract class Document_Name {
    def name: String
    def path: Path = Path.basic(name)

    override def toString: String = name
  }

  object Document_Variant {
    def parse(opt: String): Document_Variant =
      Library.space_explode('=', opt) match {
        case List(name) => Document_Variant(name, Latex.Tags.empty)
        case List(name, tags) => Document_Variant(name, Latex.Tags(tags))
        case _ => error("Malformed document variant: " + quote(opt))
      }
  }

  sealed case class Document_Variant(name: String, tags: Latex.Tags) extends Document_Name {
    def print: String = if (tags.toString.isEmpty) name else name + "=" + tags.toString
  }

  sealed case class Document_Input(name: String, sources: SHA1.Digest)
  extends Document_Name { override def toString: String = name }

  sealed case class Document_Output(name: String, sources: SHA1.Digest, log_xz: Bytes, pdf: Bytes)
  extends Document_Name {
    override def toString: String = name

    def log: String = log_xz.uncompress().text
    def log_lines: List[String] = split_lines(log)

    def write(db: SQL.Database, session_name: String): Unit =
      write_document(db, session_name, this)

    def write(dir: Path): Path = {
      val path = dir + Path.basic(name).pdf
      Isabelle_System.make_directory(path.expand.dir)
      Bytes.write(path, pdf)
      path
    }
  }


  /* SQL data model */

  object Data {
    val session_name = SQL.Column.string("session_name").make_primary_key
    val name = SQL.Column.string("name").make_primary_key
    val sources = SQL.Column.string("sources")
    val log_xz = SQL.Column.bytes("log_xz")
    val pdf = SQL.Column.bytes("pdf")

    val table = SQL.Table("isabelle_documents", List(session_name, name, sources, log_xz, pdf))

    def where_equal(session_name: String, name: String = ""): SQL.Source =
      "WHERE " + Data.session_name.equal(session_name) +
        (if (name == "") "" else " AND " + Data.name.equal(name))
  }

  def read_documents(db: SQL.Database, session_name: String): List[Document_Input] = {
    val select = Data.table.select(List(Data.name, Data.sources), Data.where_equal(session_name))
    db.using_statement(select)(stmt =>
      stmt.execute_query().iterator({ res =>
        val name = res.string(Data.name)
        val sources = res.string(Data.sources)
        Document_Input(name, SHA1.fake_digest(sources))
      }).toList)
  }

  def read_document(
    db: SQL.Database,
    session_name: String,
    name: String
  ): Option[Document_Output] = {
    val select = Data.table.select(sql = Data.where_equal(session_name, name))
    db.using_statement(select)({ stmt =>
      val res = stmt.execute_query()
      if (res.next()) {
        val name = res.string(Data.name)
        val sources = res.string(Data.sources)
        val log_xz = res.bytes(Data.log_xz)
        val pdf = res.bytes(Data.pdf)
        Some(Document_Output(name, SHA1.fake_digest(sources), log_xz, pdf))
      }
      else None
    })
  }

  def write_document(db: SQL.Database, session_name: String, doc: Document_Output): Unit = {
    db.using_statement(Data.table.insert()){ stmt =>
      stmt.string(1) = session_name
      stmt.string(2) = doc.name
      stmt.string(3) = doc.sources.toString
      stmt.bytes(4) = doc.log_xz
      stmt.bytes(5) = doc.pdf
      stmt.execute()
    }
  }


  /* background context */

  def session_background(
    options: Options,
    session: String,
    dirs: List[Path] = Nil,
    progress: Progress = new Progress,
    verbose: Boolean = false
  ): Sessions.Background = {
      Sessions.load_structure(options + "document", dirs = dirs).
        selection_deps(Sessions.Selection.session(session), progress = progress, verbose = verbose).
        background(session)
  }


  /* document context */

  val texinputs: Path = Path.explode("~~/lib/texinputs")

  val isabelle_styles: List[Path] =
    List("isabelle.sty", "isabellesym.sty", "pdfsetup.sty", "railsetup.sty").
      map(name => texinputs + Path.basic(name))

  def program_start(title: String): String =
    "PROGRAM START \"" + title + "\" ..."

  def program_running_script(title: String): String =
    "echo " + Bash.string(program_start("Running " + title)) + ";"

  def detect_program_start(s: String): Option[String] =
    for {
      s1 <- Library.try_unprefix("PROGRAM START \"", s)
      s2 <- Library.try_unsuffix("\" ...", s1)
    } yield s2

  sealed case class Document_Latex(
    name: Document.Node.Name,
    body: XML.Body,
    line_pos: Properties.T => Option[Int]
  ) {
    def content: File.Content_XML = File.content(Path.basic(tex_name(name)), body)
    def file_pos: String = File.symbolic_path(name.path)
    def write(latex_output: Latex.Output, dir: Path): Unit =
      content.output(latex_output.make(_, file_pos = file_pos, line_pos = line_pos))
        .write(dir)
  }

  def context(
    session_context: Export.Session_Context,
    document_session: Option[Sessions.Base] = None,
    document_selection: Document.Node.Name => Boolean = _ => true,
    progress: Progress = new Progress
  ): Context = new Context(session_context, document_session, document_selection, progress)

  final class Context private[Document_Build](
    val session_context: Export.Session_Context,
    document_session: Option[Sessions.Base],
    document_selection: Document.Node.Name => Boolean,
    val progress: Progress
  ) {
    context =>


    /* session info */

    private val base = document_session getOrElse session_context.session_base
    private val info = session_context.sessions_structure(base.session_name)

    def session: String = info.name
    def options: Options = info.options

    override def toString: String = session

    val classpath: List[File.Content] = session_context.classpath()

    def document_bibliography: Boolean = options.bool("document_bibliography")

    def document_logo: Option[String] =
      options.string("document_logo") match {
        case "" => None
        case "_" => Some("")
        case name => Some(name)
      }

    def document_build: String = options.string("document_build")

    def get_engine(): Engine = {
      val name = document_build
      Classpath(jar_contents = classpath).make_services(classOf[Engine])
        .find(_.name == name).getOrElse(error("Bad document_build engine " + quote(name)))
    }


    /* document content */

    def documents: List[Document_Variant] = info.documents

    def session_document_theories: List[Document.Node.Name] = base.proper_session_theories
    def all_document_theories: List[Document.Node.Name] = base.all_document_theories

    lazy val isabelle_logo: Option[File.Content] = {
      document_logo.map(logo_name =>
        Isabelle_System.with_tmp_file("logo", ext = "pdf") { tmp_path =>
          Logo.create_logo(logo_name, output_file = tmp_path, quiet = true)
          val path = Path.basic("isabelle_logo.pdf")
          val content = Bytes.read(tmp_path)
          File.content(path, content)
        })
    }

    lazy val session_graph: File.Content = {
      val path = Browser_Info.session_graph_path
      val content = graphview.Graph_File.make_pdf(options, base.session_graph_display)
      File.content(path, content)
    }

    lazy val session_tex: File.Content = {
      val path = Path.basic("session.tex")
      val content =
        Library.terminate_lines(
          session_document_theories.map(name => "\\input{" + tex_name(name) + "}"))
      File.content(path, content)
    }

    lazy val document_latex: List[Document_Latex] =
      for (name <- all_document_theories)
      yield {
        val selected = document_selection(name)

        val body =
          if (selected) {
            val entry = session_context(name.theory, Export.DOCUMENT_LATEX, permissive = true)
            YXML.parse_body(entry.text)
          }
          else {
            val text =
              proper_string(session_context.theory_source(name.theory)) getOrElse
                File.read(name.path)
            (for {
              outer <- Bibtex.Cite.parse(Bibtex.cite_commands(options), text)
              inner <- outer.parse
            } yield inner.nocite.latex_text).flatten
          }

        def line_pos(props: Properties.T): Option[Int] =
          Position.Line.unapply(props) orElse {
            if (selected) {
              for {
                snapshot <- session_context.document_snapshot
                id <- Position.Id.unapply(props)
                offset <- Position.Offset.unapply(props)
                line <- snapshot.find_command_line(id, offset)
              } yield line
            }
            else None
          }

        Document_Latex(name, body, line_pos)
      }


    /* build document */

    def build_document(doc: Document_Variant, verbose: Boolean = false): Document_Output = {
      Isabelle_System.with_tmp_dir("document") { tmp_dir =>
        val engine = get_engine()
        val directory = engine.prepare_directory(context, tmp_dir, doc)
        engine.build_document(context, directory, verbose)
      }
    }


    /* document directory */

    def make_directory(dir: Path, doc: Document_Variant): Path =
      Isabelle_System.make_directory(dir + Path.basic(doc.name))

    def prepare_directory(
      dir: Path,
      doc: Document_Variant,
      latex_output: Latex.Output
    ): Directory = {
      val doc_dir = make_directory(dir, doc)

      progress.echo(program_start("Creating directory"))


      /* actual sources: with SHA1 digest */

      isabelle_styles.foreach(Latex.copy_file(_, doc_dir))

      val comment_latex = latex_output.options.bool("document_comment_latex")
      if (!comment_latex) Latex.copy_file(texinputs + Path.basic("comment.sty"), doc_dir)
      doc.tags.sty(comment_latex).write(doc_dir)

      for ((base_dir, src) <- info.document_files) {
        Latex.copy_file_base(info.dir + base_dir, src, doc_dir)
      }

      session_tex.write(doc_dir)
      document_latex.foreach(_.write(latex_output, doc_dir))

      val root_name1 = "root_" + doc.name
      val root_name = if ((doc_dir + Path.explode(root_name1).tex).is_file) root_name1 else "root"

      val digests1 = List(doc.print, document_logo.toString, document_build).map(SHA1.digest)
      val digests2 = File.find_files(doc_dir.file, follow_links = true).map(SHA1.digest)
      val sources = SHA1.digest_set(digests1 ::: digests2)


      /* derived material: without SHA1 digest */

      isabelle_logo.foreach(_.write(doc_dir))
      session_graph.write(doc_dir)

      progress.bash("ls -alR", echo = true, cwd = doc_dir.file).check

      Directory(doc_dir, doc, root_name, sources)
    }

    def old_document(directory: Directory): Option[Document_Output] =
      for {
        db <- session_context.session_db()
        old_doc <- read_document(db, session, directory.doc.name)
        if old_doc.sources == directory.sources
      }
      yield old_doc
  }

  sealed case class Directory(
    doc_dir: Path,
    doc: Document_Variant,
    root_name: String,
    sources: SHA1.Digest
  ) {
    def root_name_script(ext: String = ""): String =
      Bash.string(if (ext.isEmpty) root_name else root_name + "." + ext)

    def conditional_script(
      ext: String, exe: String, title: String = "", after: String = ""
    ): String = {
      "if [ -f " + root_name_script(ext) + " ]\n" +
      "then\n" +
      "  " + (if (title.nonEmpty) program_running_script(title) else "") +
        exe + " " + root_name_script() + "\n" +
      (if (after.isEmpty) "" else "  " + after) +
      "fi\n"
    }

    def log_errors(): List[String] =
      Latex.latex_errors(doc_dir, root_name) :::
      Bibtex.bibtex_errors(doc_dir, root_name)

    def make_document(log: List[String], errors: List[String]): Document_Output = {
      val root_pdf = Path.basic(root_name).pdf
      val result_pdf = doc_dir + root_pdf

      if (errors.nonEmpty) {
        val message = "Failed to build document " + quote(doc.name)
        throw new Build_Error(log, errors ::: List(message))
      }
      else if (!result_pdf.is_file) {
        val message = "Bad document result: expected to find " + root_pdf
        throw new Build_Error(log, List(message))
      }
      else {
        val log_xz = Bytes(cat_lines(log)).compress()
        val pdf = Bytes.read(result_pdf)
        Document_Output(doc.name, sources, log_xz, pdf)
      }
    }
  }


  /* build engines */

  abstract class Engine(val name: String) extends Isabelle_System.Service {
    override def toString: String = name

    def prepare_directory(context: Context, dir: Path, doc: Document_Variant): Directory
    def build_document(context: Context, directory: Directory, verbose: Boolean): Document_Output
  }

  abstract class Bash_Engine(name: String) extends Engine(name) {
    def prepare_directory(context: Context, dir: Path, doc: Document_Variant): Directory =
      context.prepare_directory(dir, doc, new Latex.Output(context.options))

    def use_pdflatex: Boolean = false
    def running_latex: String = program_running_script(if (use_pdflatex) "pdflatex" else "lualatex")
    def latex_script(context: Context, directory: Directory): String =
      running_latex + (if (use_pdflatex) "$ISABELLE_PDFLATEX" else "$ISABELLE_LUALATEX") +
        " " + directory.root_name_script() + "\n"

    def bibtex_script(context: Context, directory: Directory, latex: Boolean = false): String = {
      val ext = if (context.document_bibliography) "aux" else "bib"
      directory.conditional_script(ext, "$ISABELLE_BIBTEX", title = "bibtex",
        after = if (latex) latex_script(context, directory) else "")
    }

    def makeindex_script(context: Context, directory: Directory, latex: Boolean = false): String =
      directory.conditional_script("idx", "$ISABELLE_MAKEINDEX", title = "makeindex",
        after = if (latex) latex_script(context, directory) else "")

    def use_build_script: Boolean = false
    def build_script(context: Context, directory: Directory): String = {
      val has_build_script = (directory.doc_dir + Path.explode("build")).is_file

      if (!use_build_script && has_build_script) {
        error("Unexpected document build script for option document_build=" +
          quote(context.document_build))
      }
      else if (use_build_script && !has_build_script) error("Missing document build script")
      else if (has_build_script) "./build pdf " + Bash.string(directory.doc.name)
      else {
        "set -e\n" +
        latex_script(context, directory) +
        bibtex_script(context, directory, latex = true) +
        makeindex_script(context, directory) +
        latex_script(context, directory) +
        makeindex_script(context, directory, latex = true)
      }
    }

    def build_document(
      context: Context,
      directory: Directory,
      verbose: Boolean
    ): Document_Output = {
      val result =
        context.progress.bash(
          build_script(context, directory),
          cwd = directory.doc_dir.file,
          echo = verbose,
          watchdog = Time.seconds(0.5))

      val log = result.out_lines ::: result.err_lines
      val err = result.err

      val errors1 = directory.log_errors()
      val errors2 =
        if (result.ok) errors1
        else if (err.nonEmpty) err :: errors1
        else if (errors1.nonEmpty) errors1
        else List("Error")
      directory.make_document(log, errors2)
    }
  }

  class LuaLaTeX_Engine extends Bash_Engine("lualatex")
  class PDFLaTeX_Engine extends Bash_Engine("pdflatex") { override def use_pdflatex: Boolean = true }
  class Build_Engine extends Bash_Engine("build") { override def use_build_script: Boolean = true }

  class LIPIcs_Engine(name: String) extends Bash_Engine(name) {
    def lipics_options(options: Options): Options =
      options + "document_heading_prefix=" + "document_comment_latex"

    override def use_pdflatex: Boolean = true

    override def prepare_directory(context: Context, dir: Path, doc: Document_Variant): Directory = {
      val doc_dir = context.make_directory(dir, doc)
      Build_LIPIcs.document_files.foreach(Latex.copy_file(_, doc_dir))

      val latex_output = new Latex.Output(lipics_options(context.options))
      context.prepare_directory(dir, doc, latex_output)
    }
  }
  class LIPIcs_LuaLaTeX_Engine extends LIPIcs_Engine("lipics")
  class LIPIcs_PDFLaTeX_Engine extends LIPIcs_Engine("lipics_pdflatex") {
    override def use_pdflatex: Boolean = true
  }


  /* build documents */

  def tex_name(name: Document.Node.Name): String = name.theory_base_name + ".tex"

  class Build_Error(val log_lines: List[String], val log_errors: List[String])
    extends Exn.User_Error(Exn.cat_message(log_errors: _*))

  def build_documents(
    context: Context,
    output_sources: Option[Path] = None,
    output_pdf: Option[Path] = None,
    verbose: Boolean = false
  ): List[Document_Output] = {
    val progress = context.progress
    val engine = context.get_engine()

    val documents =
      for (doc <- context.documents)
      yield {
        Isabelle_System.with_tmp_dir("document") { tmp_dir =>
          progress.echo("Preparing " + context.session + "/" + doc.name + " ...")
          val start = Time.now()

          output_sources.foreach(engine.prepare_directory(context, _, doc))
          val directory = engine.prepare_directory(context, tmp_dir, doc)

          val document =
            context.old_document(directory) getOrElse
              engine.build_document(context, directory, verbose)

          val stop = Time.now()
          val timing = stop - start

          progress.echo("Finished " + context.session + "/" + doc.name +
            " (" + timing.message_hms + " elapsed time)")

          document
        }
      }

    for (dir <- output_pdf; doc <- documents) {
      val path = doc.write(dir)
      progress.echo("Document at " + path.absolute)
    }

    documents
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("document", "prepare session theory document", Scala_Project.here,
      { args =>
        var output_sources: Option[Path] = None
        var output_pdf: Option[Path] = None
        var verbose_latex = false
        var dirs: List[Path] = Nil
        var options = Options.init()
        var verbose_build = false

        val getopts = Getopts("""
Usage: isabelle document [OPTIONS] SESSION

  Options are:
    -O DIR       output directory for LaTeX sources and resulting PDF
    -P DIR       output directory for resulting PDF
    -S DIR       output directory for LaTeX sources
    -V           verbose latex
    -d DIR       include session directory
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose build

  Prepare the theory document of a session.
""",
          "O:" -> (arg =>
            {
              val dir = Path.explode(arg)
              output_sources = Some(dir)
              output_pdf = Some(dir)
            }),
          "P:" -> (arg => { output_pdf = Some(Path.explode(arg)) }),
          "S:" -> (arg => { output_sources = Some(Path.explode(arg)) }),
          "V" -> (_ => verbose_latex = true),
          "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
          "o:" -> (arg => options = options + arg),
          "v" -> (_ => verbose_build = true))

        val more_args = getopts(args)
        val session =
          more_args match {
            case List(a) => a
            case _ => getopts.usage()
          }

        val progress = new Console_Progress(verbose = verbose_build)

        progress.interrupt_handler {
          val build_results =
            Build.build(options, selection = Sessions.Selection.session(session),
              dirs = dirs, progress = progress, verbose = verbose_build)
          if (!build_results.ok) error("Failed to build session " + quote(session))

          if (output_sources.isEmpty && output_pdf.isEmpty) {
            progress.echo_warning("No output directory")
          }

          val session_background = Document_Build.session_background(options, session, dirs = dirs)
          using(Export.open_session_context(build_results.store, session_background)) {
            session_context =>
              build_documents(
                context(session_context, progress = progress),
                output_sources = output_sources, output_pdf = output_pdf,
                verbose = verbose_latex)
          }
        }
      })
}
