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
    val full_sessions = Sessions.load(options, dirs, select_dirs)
    val (selected, selected_sessions) = full_sessions.selection(selection)

    val deps =
      Sessions.deps(selected_sessions, progress = progress, verbose = verbose,
        global_theories = full_sessions.global_theories,
        all_known = true)

    val root_keywords = Sessions.root_syntax.keywords


    if (operation_imports) {
      progress.echo("\nPotential session imports:")
      selected.flatMap(session_name =>
      {
        val info = full_sessions(session_name)
        val session_resources = new Resources(deps(session_name))

        val declared_imports =
          full_sessions.imports_ancestors(session_name).toSet + session_name
        val extra_imports =
          (for {
            (_, a) <- session_resources.session_base.known.theories.iterator
            if session_resources.theory_qualifier(a) == info.theory_qualifier
            b <- deps.all_known.get_file(Path.explode(a.node).file)
            qualifier = session_resources.theory_qualifier(b)
            if !declared_imports.contains(qualifier)
          } yield qualifier).toSet

        if (extra_imports.isEmpty) None
        else Some((session_name, extra_imports.toList.sorted, declared_imports.size))
      }).sortBy(_._3).foreach({ case (session_name, extra_imports, _) =>
        progress.echo("session " + Token.quote_name(root_keywords, session_name) + ": " +
          extra_imports.map(Token.quote_name(root_keywords, _)).mkString(" "))
      })
    }

    if (operation_repository_files) {
      progress.echo("\nMercurial files check:")
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
        selected.flatMap(session_name =>
        {
          val info = full_sessions(session_name)
          val session_base = deps(session_name)
          val session_resources = new Resources(session_base)
          val imports_base = session_base.get_imports
          val imports_resources = new Resources(imports_base)

          def standard_import(qualifier: String, dir: String, s: String): String =
          {
            val name = imports_resources.import_name(qualifier, dir, s)
            val s1 =
              if (imports_base.loaded_theory(name)) name.theory
              else {
                imports_base.known.get_file(Path.explode(name.node).file) match {
                  case Some(name1) if session_resources.theory_qualifier(name1) != qualifier =>
                    name1.theory
                  case Some(name1) if Thy_Header.is_base_name(s) =>
                    name1.theory_base_name
                  case _ => s
                }
              }
            val name2 = imports_resources.import_name(qualifier, dir, s1)
            if (name.node == name2.node) s1 else s
          }

          val updates_root =
            for {
              (_, pos) <- info.theories.flatMap(_._2)
              upd <- update_name(root_keywords, pos,
                standard_import(info.theory_qualifier, info.dir.implode, _))
            } yield upd

          val updates_theories =
            for {
              (_, name) <- session_base.known.theories_local.toList
              if session_resources.theory_qualifier(name) == info.theory_qualifier
              (_, pos) <- session_resources.check_thy(name, Token.Pos.file(name.node)).imports
              upd <- update_name(session_base.syntax.keywords, pos,
                standard_import(session_resources.theory_qualifier(name), name.master_dir, _))
            } yield upd

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
    -D DIR       include session directory and select its sessions
    -I           operation: report potential session imports
    -M           operation: Mercurial files check for imported theory files
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
        Sessions.Selection(requirements, all_sessions, exclude_session_groups,
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
        val (selected, selected_sessions) =
          Sessions.load(options, dirs, select_dirs).selection(selection)
        selected_sessions.imports_topological_order.foreach(info =>
        {
          imports(options, operation_update = operation_update, progress = progress,
            update_message = " for session " + quote(info.name),
            selection = Sessions.Selection(sessions = List(info.name)),
            dirs = dirs ::: select_dirs, verbose = verbose)
        })
      }
    })
}
