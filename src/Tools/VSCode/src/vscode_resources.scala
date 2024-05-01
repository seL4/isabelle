/*  Title:      Tools/VSCode/src/vscode_resources.scala
    Author:     Makarius

Resources for VSCode Language Server: file-system access and global state.
*/

package isabelle.vscode


import isabelle._

import java.io.{File => JFile}

import scala.util.parsing.input.Reader


object VSCode_Resources {
  /* internal state */

  sealed case class State(
    models: Map[JFile, VSCode_Model] = Map.empty,
    caret: Option[(JFile, Line.Position)] = None,
    overlays: Document.Overlays = Document.Overlays.empty,
    pending_input: Set[JFile] = Set.empty,
    pending_output: Set[JFile] = Set.empty
  ) {
    def update_models(changed: Iterable[(JFile, VSCode_Model)]): State =
      copy(
        models = models ++ changed,
        pending_input = changed.foldLeft(pending_input) { case (set, (file, _)) => set + file },
        pending_output = changed.foldLeft(pending_output) { case (set, (file, _)) => set + file })

    def update_caret(new_caret: Option[(JFile, Line.Position)]): State =
      if (caret == new_caret) this
      else
        copy(
          caret = new_caret,
          pending_input = pending_input ++ caret.map(_._1) ++ new_caret.map(_._1))

    def get_caret(file: JFile): Option[Line.Position] =
      caret match {
        case Some((caret_file, caret_pos)) if caret_file == file => Some(caret_pos)
        case _ => None
      }

    lazy val document_blobs: Document.Blobs =
      Document.Blobs(
        (for {
          (_, model) <- models.iterator
          blob <- model.get_blob
        } yield (model.node_name -> blob)).toMap)

    def change_overlay(insert: Boolean, file: JFile,
        command: Command, fn: String, args: List[String]): State =
      copy(
        overlays =
          if (insert) overlays.insert(command, fn, args)
          else overlays.remove(command, fn, args),
        pending_input = pending_input + file)
  }


  /* caret */

  sealed case class Caret(file: JFile, model: VSCode_Model, offset: Text.Offset) {
    def node_name: Document.Node.Name = model.node_name
  }
}

class VSCode_Resources(
  val options: Options,
  session_background: Sessions.Background,
  log: Logger = new Logger)
extends Resources(session_background, log = log) {
  resources =>

  private val state = Synchronized(VSCode_Resources.State())


  /* options */

  def pide_extensions: Boolean = options.bool("vscode_pide_extensions")
  def unicode_symbols: Boolean = options.bool("vscode_unicode_symbols")
  def html_output: Boolean = options.bool("vscode_html_output")
  def tooltip_margin: Int = options.int("vscode_tooltip_margin")
  def message_margin: Int = options.int("vscode_message_margin")


  /* document node name */

  def node_file(name: Document.Node.Name): JFile = new JFile(name.node)

  def node_name(file: JFile): Document.Node.Name =
    find_theory(file) getOrElse {
      val node = file.getPath
      val theory = theory_name(Sessions.DRAFT, Thy_Header.theory_name(node))
      if (session_base.loaded_theory(theory)) Document.Node.Name.loaded_theory(theory)
      else Document.Node.Name(node, theory = theory)
    }

  override def migrate_name(standard_name: Document.Node.Name): Document.Node.Name =
    node_name(Path.explode(standard_name.node).canonical_file)

  override def append_path(prefix: String, source_path: Path): String = {
    val path = source_path.expand
    if (prefix == "" || path.is_absolute) File.platform_path(path)
    else if (path.is_current) prefix
    else if (path.is_basic && !prefix.endsWith("/") && !prefix.endsWith(JFile.separator))
      prefix + JFile.separator + File.platform_path(path)
    else if (path.is_basic) prefix + File.platform_path(path)
    else File.absolute(new JFile(prefix + JFile.separator + File.platform_path(path))).getPath
  }

  override def read_dir(dir: String): List[String] =
    File.read_dir(Path.explode(File.standard_path(dir)))

  def get_models(): Iterable[VSCode_Model] = state.value.models.values
  def get_model(file: JFile): Option[VSCode_Model] = state.value.models.get(file)
  def get_model(name: Document.Node.Name): Option[VSCode_Model] = get_model(node_file(name))


  /* snapshot */

  def snapshot(model: VSCode_Model): Document.Snapshot =
    model.session.snapshot(
      node_name = model.node_name,
      pending_edits = Document.Pending_Edits.make(get_models()))

  def get_snapshot(file: JFile): Option[Document.Snapshot] =
    get_model(file).map(snapshot)

  def get_snapshot(name: Document.Node.Name): Option[Document.Snapshot] =
    get_model(name).map(snapshot)


  /* rendering */

  def rendering(snapshot: Document.Snapshot, model: VSCode_Model): VSCode_Rendering =
    new VSCode_Rendering(snapshot, model)

  def rendering(model: VSCode_Model): VSCode_Rendering = rendering(snapshot(model), model)

  def get_rendering(file: JFile): Option[VSCode_Rendering] =
    get_model(file).map(rendering)

  def get_rendering(name: Document.Node.Name): Option[VSCode_Rendering] =
    get_model(name).map(rendering)


  /* file content */

  def read_file_content(name: Document.Node.Name): Option[String] = {
    make_theory_content(name) orElse {
      try { Some(Line.normalize(File.read(node_file(name)))) }
      catch { case ERROR(_) => None }
    }
  }

  def get_file_content(name: Document.Node.Name): Option[String] =
    get_model(name) match {
      case Some(model) => Some(model.content.text)
      case None => read_file_content(name)
    }

  override def with_thy_reader[A](name: Document.Node.Name, f: Reader[Char] => A): A = {
    val file = node_file(name)
    get_model(file) match {
      case Some(model) => f(Scan.char_reader(model.content.text))
      case None if file.isFile => using(Scan.byte_reader(file))(f)
      case None => error("No such file: " + quote(file.toString))
    }
  }


  /* document models */

  def visible_node(name: Document.Node.Name): Boolean =
    get_model(name) match {
      case Some(model) => model.node_visible
      case None => false
    }

  def change_model(
    session: Session,
    editor: Language_Server.Editor,
    file: JFile,
    version: Long,
    text: String,
    range: Option[Line.Range] = None
  ): Unit = {
    state.change { st =>
      val model = st.models.getOrElse(file, VSCode_Model.init(session, editor, node_name(file)))
      val model1 =
        (model.change_text(text, range) getOrElse model).set_version(version).external(false)
      st.update_models(Some(file -> model1))
    }
  }

  def close_model(file: JFile): Boolean =
    state.change_result(st =>
      st.models.get(file) match {
        case None => (false, st)
        case Some(model) => (true, st.update_models(Some(file -> model.external(true))))
      })

  def sync_models(changed_files: Set[JFile]): Unit =
    state.change { st =>
      val changed_models =
        (for {
          (file, model) <- st.models.iterator
          if changed_files(file) && model.external_file
          text <- read_file_content(model.node_name)
          model1 <- model.change_text(text)
        } yield (file, model1)).toList
      st.update_models(changed_models)
    }


  /* overlays */

  def node_overlays(name: Document.Node.Name): Document.Node.Overlays =
    state.value.overlays(name)

  def insert_overlay(command: Command, fn: String, args: List[String]): Unit =
    state.change(_.change_overlay(true, node_file(command.node_name), command, fn, args))

  def remove_overlay(command: Command, fn: String, args: List[String]): Unit =
    state.change(_.change_overlay(false, node_file(command.node_name), command, fn, args))


  /* resolve dependencies */

  def resolve_dependencies(
    session: Session,
    editor: Language_Server.Editor,
    file_watcher: File_Watcher
  ): (Boolean, Boolean) = {
    state.change_result { st =>
      val stable_tip_version = session.stable_tip_version(st.models.values)

      val thy_files =
        resources.resolve_dependencies(st.models.values, editor.document_required())

      val aux_files = stable_tip_version.toList.flatMap(undefined_blobs)

      val loaded_models =
        (for {
          node_name <- thy_files.iterator ++ aux_files.iterator
          file = node_file(node_name)
          if !st.models.isDefinedAt(file)
          text <- { file_watcher.register_parent(file); read_file_content(node_name) }
        }
        yield {
          val model = VSCode_Model.init(session, editor, node_name)
          val model1 = (model.change_text(text) getOrElse model).external(true)
          (file, model1)
        }).toList

      val invoke_input = loaded_models.nonEmpty
      val invoke_load = stable_tip_version.isEmpty

      ((invoke_input, invoke_load), st.update_models(loaded_models))
    }
  }


  /* pending input */

  def flush_input(session: Session, channel: Channel): Unit = {
    state.change { st =>
      val changed_models =
        (for {
          file <- st.pending_input.iterator
          model <- st.models.get(file)
          (edits, model1) <-
            model.flush_edits(false, st.document_blobs, file, st.get_caret(file))
        } yield (edits, (file, model1))).toList

      for { ((workspace_edits, _), _) <- changed_models if workspace_edits.nonEmpty }
        channel.write(LSP.WorkspaceEdit(workspace_edits))

      session.update(st.document_blobs, changed_models.flatMap(res => res._1._2))

      st.copy(
        models = st.models ++ changed_models.iterator.map(_._2),
        pending_input = Set.empty)
    }
  }


  /* pending output */

  def update_output(changed_nodes: Iterable[JFile]): Unit =
    state.change(st => st.copy(pending_output = st.pending_output ++ changed_nodes))

  def update_output_visible(): Unit =
    state.change(st => st.copy(pending_output = st.pending_output ++
      (for ((file, model) <- st.models.iterator if model.node_visible) yield file)))

  def flush_output(channel: Channel): Boolean = {
    state.change_result { st =>
      val (postponed, flushed) =
        (for {
          file <- st.pending_output.iterator
          model <- st.models.get(file)
        } yield (file, model, rendering(model))).toList.partition(_._3.snapshot.is_outdated)

      val changed_iterator =
        for {
          (file, model, rendering) <- flushed.iterator
          (changed_diags, changed_decos, model1) = model.publish(rendering)
          if changed_diags.isDefined || changed_decos.isDefined
        }
        yield {
          for (diags <- changed_diags)
            channel.write(LSP.PublishDiagnostics(file, rendering.diagnostics_output(diags)))
          if (pide_extensions) {
            for (decos <- changed_decos)
              channel.write(rendering.decoration_output(decos).json(file))
          }
          (file, model1)
        }

      (postponed.nonEmpty,
        st.copy(
          models = st.models ++ changed_iterator,
          pending_output = postponed.map(_._1).toSet))
    }
  }


  /* output text */

  def output_text(text: String): String =
    Symbol.output(unicode_symbols, text)

  def output_xml(xml: XML.Tree): String =
    output_text(XML.content(xml))

  def output_pretty(body: XML.Body, margin: Int): String =
    output_text(Pretty.string_of(body, margin = margin, metric = Symbol.Metric))
  def output_pretty_tooltip(body: XML.Body): String = output_pretty(body, tooltip_margin)
  def output_pretty_message(body: XML.Body): String = output_pretty(body, message_margin)


  /* caret handling */

  def update_caret(caret: Option[(JFile, Line.Position)]): Unit =
    state.change(_.update_caret(caret))

  def get_caret(): Option[VSCode_Resources.Caret] = {
    val st = state.value
    for {
      (file, pos) <- st.caret
      model <- st.models.get(file)
      offset <- model.content.doc.offset(pos)
    }
    yield VSCode_Resources.Caret(file, model, offset)
  }


  /* spell checker */

  val spell_checker = new Spell_Checker_Variable
  spell_checker.update(options)
}
