/*  Title:      Pure/Tools/imports.scala
    Author:     Makarius

Maintain theory imports wrt. session structure.
*/

package isabelle


import java.io.{File => JFile}


object Imports
{
  /* repository files */

  def repository_files(progress: Progress, start: Path, pred: JFile => Boolean = _ => true)
      : List[JFile] =
    Mercurial.find_repository(start) match {
      case None =>
        progress.echo_warning("Ignoring directory " + start + " (no Mercurial repository)")
        Nil
      case Some(hg) =>
        val start_path = start.canonical_file.toPath
        for {
          name <- hg.known_files()
          file = (hg.root + Path.explode(name)).file
          if pred(file) && File.canonical(file).toPath.startsWith(start_path)
        } yield file
    }


  /* report imports */

  sealed case class Report(
    info: Sessions.Info,
    declared_imports: Set[String],
    potential_imports: Option[List[String]],
    actual_imports: Option[List[String]])
  {
    def print(keywords: Keyword.Keywords, result: List[String]): String =
    {
      def print_name(name: String): String = Token.quote_name(keywords, name)

      "  session " + print_name(info.name) + ": " + result.map(print_name(_)).mkString(" ")
    }
  }


  /* update imports */

  sealed case class Update(range: Text.Range, old_text: String, new_text: String)
  {
    def edits: List[Text.Edit] =
      Text.Edit.replace(range.start, old_text, new_text)

    override def toString: String =
      range.toString + ": " + old_text + " -> " + new_text
  }

  def update_name(keywords: Keyword.Keywords, pos: Position.T, update: String => String)
    : Option[(JFile, Update)] =
  {
    val file =
      pos match {
        case Position.File(file) => Path.explode(file).canonical_file
        case _ => error("Missing file in position" + Position.here(pos))
      }

    val text = File.read(file)

    val range =
      pos match {
        case Position.Range(symbol_range) => Symbol.Text_Chunk(text).decode(symbol_range)
        case _ => error("Missing range in position" + Position.here(pos))
      }

    Token.read_name(keywords, range.substring(text)) match {
      case Some(tok) =>
        val s1 = tok.source
        val s2 = Token.quote_name(keywords, update(tok.content))
        if (s1 == s2) None else Some((file, Update(range, s1, s2)))
      case None => error("Name token expected" + Position.here(pos))
    }
  }


  /* collective operations */

  def imports(
    options: Options,
    operation_imports: Boolean = false,
    operation_repository_files: Boolean = false,
    operation_update: Boolean = false,
    update_message: String = "",
    progress: Progress = No_Progress,
    selection: Sessions.Selection = Sessions.Selection.empty,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    verbose: Boolean = false) =
  {
    val sessions_structure =
      Sessions.load_structure(options, dirs = dirs, select_dirs = select_dirs)

    val deps =
      sessions_structure.selection_deps(options, selection, progress = progress, verbose = verbose).
        check_errors

    val root_keywords = Sessions.root_syntax.keywords

    if (operation_imports) {
      val report_imports: List[Report] =
        sessions_structure.build_topological_order.map((session_name: String) =>
          {
            val info = sessions_structure(session_name)
            val session_base = deps(session_name)

            val declared_imports =
              sessions_structure.imports_requirements(List(session_name)).toSet

            val extra_imports =
              (for {
                a <- session_base.known.theory_names
                if session_base.theory_qualifier(a) == info.name
                b <- deps.all_known.get_file(a.path.file)
                qualifier = session_base.theory_qualifier(b)
                if !declared_imports.contains(qualifier)
              } yield qualifier).toSet

            val loaded_imports =
              sessions_structure.imports_requirements(
                session_base.loaded_theories.keys.map(a =>
                  session_base.theory_qualifier(session_base.known.theories(a).name)))
              .toSet - session_name

            val minimal_imports =
              loaded_imports.filter(s1 =>
                !loaded_imports.exists(s2 => sessions_structure.imports_graph.is_edge(s1, s2)))

            def make_result(set: Set[String]): Option[List[String]] =
              if (set.isEmpty) None
              else Some(sessions_structure.imports_topological_order.filter(set))

            Report(info, declared_imports, make_result(extra_imports),
              if (loaded_imports == declared_imports - session_name) None
              else make_result(minimal_imports))
          })

      progress.echo("\nPotential session imports:")
      for {
        report <- report_imports.sortBy(_.declared_imports.size)
        potential_imports <- report.potential_imports
      } progress.echo(report.print(root_keywords, potential_imports))

      progress.echo("\nActual session imports:")
      for {
        report <- report_imports
        actual_imports <- report.actual_imports
      } progress.echo(report.print(root_keywords, actual_imports))
    }

    if (operation_repository_files) {
      progress.echo("\nMercurial repository check:")
      val unused_files =
        for {
          (_, dir) <- Sessions.directories(dirs, select_dirs)
          file <- repository_files(progress, dir, file => file.getName.endsWith(".thy"))
          if deps.all_known.get_file(file).isEmpty
        } yield file
      unused_files.foreach(file => progress.echo("unused file " + quote(file.toString)))
    }

    if (operation_update) {
      progress.echo("\nUpdate theory imports" + update_message + ":")
      val updates =
        sessions_structure.build_topological_order.flatMap(session_name =>
          {
            val info = sessions_structure(session_name)
            val session_base = deps(session_name)
            val session_resources = new Resources(sessions_structure, session_base)
            val imports_base = session_base.get_imports
            val imports_resources = new Resources(sessions_structure, imports_base)

            def standard_import(qualifier: String, dir: String, s: String): String =
              imports_resources.standard_import(session_base, qualifier, dir, s)

            val updates_root =
              for {
                (_, pos) <- info.theories.flatMap(_._2)
                upd <- update_name(root_keywords, pos, standard_import(info.name, info.dir.implode, _))
              } yield upd

            val updates_theories =
              (for {
                name <- session_base.known.theories_local.iterator.map(p => p._2.name)
                if session_base.theory_qualifier(name) == info.name
                (_, pos) <- session_resources.check_thy(name, Token.Pos.file(name.node)).imports_pos
                upd <- update_name(session_base.overall_syntax.keywords, pos,
                  standard_import(session_base.theory_qualifier(name), name.master_dir, _))
              } yield upd).toList

            updates_root ::: updates_theories
          })

      val file_updates = (Multi_Map.empty[JFile, Update] /: updates)(_ + _)
      val conflicts =
        file_updates.iterator_list.flatMap({ case (file, upds) =>
          Library.duplicates(upds.sortBy(_.range.start),
            (x: Update, y: Update) => x.range overlaps y.range) match
          {
            case Nil => None
            case bad => Some((file, bad))
          }
        })
      if (conflicts.nonEmpty)
        error(cat_lines(
          conflicts.map({ case (file, bad) =>
            "Conflicting updates for file " + file + bad.mkString("\n  ", "\n  ", "") })))

      for ((file, upds) <- file_updates.iterator_list.toList.sortBy(p => p._1.toString)) {
        progress.echo("file " + quote(file.toString))
        val edits =
          upds.sortBy(upd => - upd.range.start).flatMap(upd =>
            Text.Edit.replace(upd.range.start, upd.old_text, upd.new_text))
        val new_text =
          (File.read(file) /: edits)({ case (text, edit) =>
            edit.edit(text, 0) match {
              case (None, text1) => text1
              case (Some(_), _) => error("Failed to apply edit " + edit + " to file " + file)
            }
          })
        File.write_backup2(Path.explode(File.standard_path(file)), new_text)
      }
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("imports", "maintain theory imports wrt. session structure", args =>
    {
      var base_sessions: List[String] = Nil
      var select_dirs: List[Path] = Nil
      var operation_imports = false
      var operation_repository_files = false
      var requirements = false
      var operation_update = false
      var exclude_session_groups: List[String] = Nil
      var all_sessions = false
      var dirs: List[Path] = Nil
      var session_groups: List[String] = Nil
      var incremental_update = false
      var options = Options.init()
      var verbose = false
      var exclude_sessions: List[String] = Nil

      val getopts = Getopts("""
Usage: isabelle imports [OPTIONS] [SESSIONS ...]

  Options are:
    -B NAME      include session NAME and all descendants
    -D DIR       include session directory and select its sessions
    -I           operation: report session imports
    -M           operation: Mercurial repository check for theory files
    -R           operate on requirements of selected sessions
    -U           operation: update theory imports to use session qualifiers
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -d DIR       include session directory
    -g NAME      select session group NAME
    -i           incremental update according to session graph structure
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose
    -x NAME      exclude session NAME and all descendants

  Maintain theory imports wrt. session structure. At least one operation
  needs to be specified (see options -I -M -U).
""",
      "B:" -> (arg => base_sessions = base_sessions ::: List(arg)),
      "D:" -> (arg => select_dirs = select_dirs ::: List(Path.explode(arg))),
      "I" -> (_ => operation_imports = true),
      "M" -> (_ => operation_repository_files = true),
      "R" -> (_ => requirements = true),
      "U" -> (_ => operation_update = true),
      "X:" -> (arg => exclude_session_groups = exclude_session_groups ::: List(arg)),
      "a" -> (_ => all_sessions = true),
      "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
      "g:" -> (arg => session_groups = session_groups ::: List(arg)),
      "i" -> (_ => incremental_update = true),
      "o:" -> (arg => options = options + arg),
      "v" -> (_ => verbose = true),
      "x:" -> (arg => exclude_sessions = exclude_sessions ::: List(arg)))

      val sessions = getopts(args)
      if (args.isEmpty || !(operation_imports || operation_repository_files || operation_update))
        getopts.usage()

      val selection =
        Sessions.Selection(requirements, all_sessions, base_sessions, exclude_session_groups,
          exclude_sessions, session_groups, sessions)

      val progress = new Console_Progress(verbose = verbose)

      if (operation_imports || operation_repository_files ||
          operation_update && !incremental_update)
      {
        imports(options, operation_imports = operation_imports,
          operation_repository_files = operation_repository_files,
          operation_update = operation_update,
          progress = progress, selection = selection, dirs = dirs, select_dirs = select_dirs,
          verbose = verbose)
      }
      else if (operation_update && incremental_update) {
        Sessions.load_structure(options, dirs = dirs, select_dirs = select_dirs).
          selection(selection).imports_topological_order.foreach(name =>
            {
              imports(options, operation_update = operation_update, progress = progress,
                update_message = " for session " + quote(name),
                selection = Sessions.Selection(sessions = List(name)),
                dirs = dirs ::: select_dirs, verbose = verbose)
            })
      }
    })
}
