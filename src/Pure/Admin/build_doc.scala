/*  Title:      Pure/Admin/build_doc.scala
    Author:     Makarius

Build Isabelle documentation.
*/

package isabelle


import java.io.{File => JFile}


object Build_Doc
{
  /* build_doc */

  def build_doc(
    options: Options,
    progress: Progress = new Progress,
    all_docs: Boolean = false,
    max_jobs: Int = 1,
    docs: List[String] = Nil)
  {
    val store = Sessions.store(options)

    val sessions_structure = Sessions.load_structure(options)
    val selected =
      for {
        session <- sessions_structure.build_topological_order
        info = sessions_structure(session)
        if info.groups.contains("doc")
        doc = info.options.string("document_variants")
        if all_docs || docs.contains(doc)
      } yield (doc, session)

    val documents = selected.map(_._1)
    val selection = Sessions.Selection(sessions = selected.map(_._2))

    docs.filter(doc => !documents.contains(doc)) match {
      case Nil =>
      case bad => error("No documentation session for " + commas_quote(bad))
    }

    progress.echo("Build started for sessions " + commas_quote(selection.sessions))
    Build.build(options, selection = selection, progress = progress, max_jobs = max_jobs).ok ||
      error("Build failed")

    progress.echo("Build started for documentation " + commas_quote(documents))
    val doc_options =
      options + "document=pdf" + "document_output=~~/doc" + "document_output_sources=false"
    val deps = Sessions.load_structure(doc_options).selection_deps(selection)
    for (session <- selection.sessions) {
      progress.expose_interrupt()
      Present.build_documents(session, deps, store, progress = progress)
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("build_doc", "build Isabelle documentation", args =>
    {
      var all_docs = false
      var max_jobs = 1
      var options = Options.init()

      val getopts =
        Getopts("""
Usage: isabelle build_doc [OPTIONS] [DOCS ...]

  Options are:
    -a           select all documentation sessions
    -j INT       maximum number of parallel jobs (default 1)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)

  Build Isabelle documentation from documentation sessions with
  suitable document_variants entry.
""",
          "a" -> (_ => all_docs = true),
          "j:" -> (arg => max_jobs = Value.Int.parse(arg)),
          "o:" -> (arg => options = options + arg))

      val docs = getopts(args)

      if (!all_docs && docs.isEmpty) getopts.usage()

      val progress = new Console_Progress()

      progress.interrupt_handler {
        build_doc(options, progress, all_docs, max_jobs, docs)
      }
    })
}
