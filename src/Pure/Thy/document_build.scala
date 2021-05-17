/*  Title:      Pure/Thy/document_build.scala
    Author:     Makarius

Build theory document (PDF) from session database.
*/

package isabelle


object Document_Build
{
  /* document variants */

  abstract class Document_Name
  {
    def name: String
    def path: Path = Path.basic(name)

    override def toString: String = name
  }

  object Document_Variant
  {
    def parse(name: String, tags: String): Document_Variant =
      Document_Variant(name, Library.space_explode(',', tags))

    def parse(opt: String): Document_Variant =
      Library.space_explode('=', opt) match {
        case List(name) => Document_Variant(name, Nil)
        case List(name, tags) => parse(name, tags)
        case _ => error("Malformed document variant: " + quote(opt))
      }
  }

  sealed case class Document_Variant(name: String, tags: List[String]) extends Document_Name
  {
    def print_tags: String = tags.mkString(",")
    def print: String = if (tags.isEmpty) name else name + "=" + print_tags

    def latex_sty: String =
      Library.terminate_lines(
        tags.map(tag =>
          tag.toList match {
            case '/' :: cs => "\\isafoldtag{" + cs.mkString + "}"
            case '-' :: cs => "\\isadroptag{" + cs.mkString + "}"
            case '+' :: cs => "\\isakeeptag{" + cs.mkString + "}"
            case cs => "\\isakeeptag{" + cs.mkString + "}"
          }))
  }

  sealed case class Document_Input(name: String, sources: SHA1.Digest)
    extends Document_Name

  sealed case class Document_Output(name: String, sources: SHA1.Digest, log_xz: Bytes, pdf: Bytes)
    extends Document_Name
  {
    def log: String = log_xz.uncompress().text
    def log_lines: List[String] = split_lines(log)

    def write(db: SQL.Database, session_name: String): Unit =
      write_document(db, session_name, this)
  }


  /* SQL data model */

  object Data
  {
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

  def read_documents(db: SQL.Database, session_name: String): List[Document_Input] =
  {
    val select = Data.table.select(List(Data.name, Data.sources), Data.where_equal(session_name))
    db.using_statement(select)(stmt =>
      stmt.execute_query().iterator(res =>
      {
        val name = res.string(Data.name)
        val sources = res.string(Data.sources)
        Document_Input(name, SHA1.fake(sources))
      }).toList)
  }

  def read_document(db: SQL.Database, session_name: String, name: String): Option[Document_Output] =
  {
    val select = Data.table.select(sql = Data.where_equal(session_name, name))
    db.using_statement(select)(stmt =>
    {
      val res = stmt.execute_query()
      if (res.next()) {
        val name = res.string(Data.name)
        val sources = res.string(Data.sources)
        val log_xz = res.bytes(Data.log_xz)
        val pdf = res.bytes(Data.pdf)
        Some(Document_Output(name, SHA1.fake(sources), log_xz, pdf))
      }
      else None
    })
  }

  def write_document(db: SQL.Database, session_name: String, doc: Document_Output): Unit =
  {
    db.using_statement(Data.table.insert())(stmt =>
    {
      stmt.string(1) = session_name
      stmt.string(2) = doc.name
      stmt.string(3) = doc.sources.toString
      stmt.bytes(4) = doc.log_xz
      stmt.bytes(5) = doc.pdf
      stmt.execute()
    })
  }



  /* build documents */

  val session_tex_path = Path.explode("session.tex")

  def tex_name(name: Document.Node.Name): String = name.theory_base_name + ".tex"
  def document_tex_name(name: Document.Node.Name): String = "document/" + tex_name(name)

  class Build_Error(val log_lines: List[String], val message: String)
    extends Exn.User_Error(message)

  def build_documents(
    session: String,
    deps: Sessions.Deps,
    db_context: Sessions.Database_Context,
    progress: Progress = new Progress,
    output_sources: Option[Path] = None,
    output_pdf: Option[Path] = None,
    verbose: Boolean = false,
    verbose_latex: Boolean = false): List[Document_Output] =
  {
    /* session info */

    val info = deps.sessions_structure(session)
    val hierarchy = deps.sessions_structure.hierarchy(session)
    val options = info.options
    val base = deps(session)
    val graph_pdf = graphview.Graph_File.make_pdf(options, base.session_graph_display)


    /* prepare document directory */

    lazy val tex_files =
      for (name <- base.session_theories ::: base.document_theories)
      yield {
        val entry = db_context.get_export(hierarchy, name.theory, document_tex_name(name))
        Path.basic(tex_name(name)) -> entry.uncompressed
      }

    def prepare_dir1(dir: Path, doc: Document_Variant): (Path, String) =
    {
      val doc_dir = dir + Path.basic(doc.name)
      Isabelle_System.make_directory(doc_dir)

      Isabelle_System.bash("isabelle latex -o sty", cwd = doc_dir.file).check
      File.write(doc_dir + Path.explode("isabelletags.sty"), doc.latex_sty)
      for ((base_dir, src) <- info.document_files) {
        Isabelle_System.copy_file_base(info.dir + base_dir, src, doc_dir)
      }

      File.write(doc_dir + session_tex_path,
        Library.terminate_lines(
          base.session_theories.map(name => "\\input{" + tex_name(name) + "}")))

      for ((path, tex) <- tex_files) Bytes.write(doc_dir + path, tex)

      val root1 = "root_" + doc.name
      val root = if ((doc_dir + Path.explode(root1).tex).is_file) root1 else "root"

      (doc_dir, root)
    }

    def prepare_dir2(dir: Path, doc: Document_Variant): Unit =
    {
      val doc_dir = dir + Path.basic(doc.name)

      // non-deterministic, but irrelevant
      Bytes.write(doc_dir + Presentation.session_graph_path, graph_pdf)
    }


    /* produce documents */

    val documents =
      for (doc <- info.documents)
      yield {
        Isabelle_System.with_tmp_dir("document")(tmp_dir =>
        {
          progress.echo("Preparing " + session + "/" + doc.name + " ...")
          val start = Time.now()


          // prepare sources

          val (doc_dir, root) = prepare_dir1(tmp_dir, doc)
          val digests = File.find_files(doc_dir.file, follow_links = true).map(SHA1.digest)
          val sources = SHA1.digest_set(digests)
          prepare_dir2(tmp_dir, doc)

          for (dir <- output_sources) {
            prepare_dir1(dir, doc)
            prepare_dir2(dir, doc)
          }


          // old document from database

          val old_document =
            for {
              old_doc <- db_context.input_database(session)(read_document(_, _, doc.name))
              if old_doc.sources == sources
            }
            yield {
              Bytes.write(doc_dir + doc.path.pdf, old_doc.pdf)
              old_doc
            }

          old_document getOrElse {
            // bash scripts

            def root_bash(ext: String): String = Bash.string(root + "." + ext)

            def latex_bash(fmt: String = "pdf", ext: String = "tex"): String =
              "isabelle latex -o " + Bash.string(fmt) + " " + Bash.string(root + "." + ext)

            def bash(items: String*): Process_Result =
              progress.bash(items.mkString(" && "), cwd = doc_dir.file,
                echo = verbose_latex, watchdog = Time.seconds(0.5))


            // prepare document

            val result =
              if ((doc_dir + Path.explode("build")).is_file) {
                bash("./build pdf " + Bash.string(doc.name))
              }
              else {
                bash(
                  latex_bash(),
                  "{ [ ! -f " + root_bash("bib") + " ] || " + latex_bash("bbl") + "; }",
                  "{ [ ! -f " + root_bash("idx") + " ] || " + latex_bash("idx") + "; }",
                  latex_bash(),
                  latex_bash())
              }


            // result

            val root_pdf = Path.basic(root).pdf
            val result_path = doc_dir + root_pdf

            val log_lines = result.out_lines ::: result.err_lines

            val errors =
              (if (result.ok) Nil else List(result.err)) :::
              Latex.latex_errors(doc_dir, root) :::
              Bibtex.bibtex_errors(doc_dir, root)

            if (errors.nonEmpty) {
              val message =
                Exn.cat_message(
                  (errors ::: List("Failed to build document " + quote(doc.name))):_*)
              throw new Build_Error(log_lines, message)
            }
            else if (!result_path.is_file) {
              val message = "Bad document result: expected to find " + root_pdf
              throw new Build_Error(log_lines, message)
            }
            else {
              val stop = Time.now()
              val timing = stop - start
              progress.echo("Finished " + session + "/" + doc.name +
                " (" + timing.message_hms + " elapsed time)")

              val log_xz = Bytes(cat_lines(log_lines)).compress()
              val pdf = Bytes.read(result_path)
              Document_Output(doc.name, sources, log_xz, pdf)
            }
          }
        })
      }

    for (dir <- output_pdf; doc <- documents) {
      Isabelle_System.make_directory(dir)
      val path = dir + doc.path.pdf
      Bytes.write(path, doc.pdf)
      progress.echo("Document at " + path.absolute)
    }

    documents
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("document", "prepare session theory document", Scala_Project.here, args =>
    {
      var output_sources: Option[Path] = None
      var output_pdf: Option[Path] = None
      var verbose_latex = false
      var dirs: List[Path] = Nil
      var options = Options.init()
      var verbose_build = false

      val getopts = Getopts(
        """
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
      val store = Sessions.store(options)

      progress.interrupt_handler {
        val res =
          Build.build(options, selection = Sessions.Selection.session(session),
            dirs = dirs, progress = progress, verbose = verbose_build)
        if (!res.ok) error("Failed to build session " + quote(session))

        val deps =
          Sessions.load_structure(options + "document=pdf", dirs = dirs).
            selection_deps(Sessions.Selection.session(session))

        if (output_sources.isEmpty && output_pdf.isEmpty) {
          progress.echo_warning("No output directory")
        }

        using(store.open_database_context())(db_context =>
          build_documents(session, deps, db_context, progress = progress,
            output_sources = output_sources, output_pdf = output_pdf,
            verbose = true, verbose_latex = verbose_latex))
      }
    })
}
