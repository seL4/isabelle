/*  Title:      Tools/VSCode/extension/src/extension.scala
    Author:     Makarius
    Author:     Denis Paluca, TU Muenchen
    Author:     Fabian Huch, TU Muenchen

Isabelle/VSCode extension.
*/

package isabelle.vscode.extension

import scala.collection.mutable
import scala.scalajs.js

import VSCode.{Uri, Text_Editor, Workspace, Window, Commands, Language_Client}

import isabelle._
import isabelle.vscode.LSP


object Extension extends VSCode.Extension {
  private var last_caret_update: Option[LSP.Caret_Update] = None
  private var last_visible_editors: List[Text_Editor] = Nil


  /* command-line arguments from "isabelle vscode" */

  def print_value(x: Any): String = x match { case x: String => x case _ => JSON.Format(x) }

  def isabelle_options(args: JSON.T): List[String] = {
    val result = new mutable.ListBuffer[String]
    def add(s: String): Unit = { result += s }
    def add_value(opt: String, slot: String): Unit = {
      val x = JSON.string(args, slot)
      x.foreach { x => add(opt); add(print_value(x)) }
    }
    def add_values(opt: String, slot: String): Unit =
      JSON.value(args, slot) match {
        case Some(xs: List[_]) =>
          for (x <- xs) { add(opt); add(print_value(x)) }
        case _ =>
      }

    add_value("-A", "logic_ancestor")
    add_value(if (JSON.bool(args, "logic_requirements").contains(true)) "-R" else "-l", "logic")

    add_values("-d", "session_dirs")
    add_values("-i", "include_sessions")
    add_values("-m", "modes")
    add_values("-n", "no_build")
    add_value("-L", "log_file")
    if (JSON.bool(args, "verbose").contains(true)) { add("-v") }

    val config = Workspace.configuration("isabelle.options")
    config.entries.collect {
      case (key, value: String) =>
        if (value != "") {
          add("-o"); add(Options.Spec.eq(key, value).print)
        }
    }
    add_values("-o", "options")

    result.result()
  }


  /* activate extension */

  @js.annotation.JSExportTopLevel("activate")
  def activate(ctxt: VSCode.Extension.Ctxt): Unit = {
    /* server */

    val context = VSCode.Extension.context(ctxt)

    try {
      val isabelle_home = Isabelle_System.getenv_strict("ISABELLE_HOME")
      val isabelle_tool = isabelle_home + "/bin/isabelle"
      val args =
        JSON.parse(proper_string(Isabelle_System.getenv("ISABELLE_VSCODIUM_ARGS")).getOrElse("{}"))

      val server_opts = isabelle_options(args)
      val server_options =
        if (Platform.is_windows)
          Language_Client.Server_Options(command = setup.Environment.cygwin_root() + "\\bin\\bash",
            args = List("-l", isabelle_tool, "vscode_server") ::: server_opts)
        else
          Language_Client.Server_Options(command = isabelle_tool,
            args = "vscode_server" :: server_opts)

      val language_client_options =
        Language_Client.Options(document_selector =
          List(
            Language_Client.Document_Filter("isabelle", scheme = VSCode_Lib.file_scheme),
            Language_Client.Document_Filter("isabelle-ml", scheme = VSCode_Lib.file_scheme),
            Language_Client.Document_Filter("bibtex", scheme = VSCode_Lib.file_scheme)))

      val language_client = Language_Client("Isabelle", server_options, language_client_options)

      Window.with_progress { progress =>
        progress.report("Waiting for Isabelle language server...")
        language_client.on_ready()
      }


      /* decorations */

      Decorations.setup(context)
      context.subscribe(
        Workspace.on_change_configuration(_ => Decorations.setup(context)),
        Workspace.on_change_document(event => Decorations.touch_document(event.document)),
        Window.on_change_active_editor(_.foreach(Decorations.update_editor)),
        Workspace.on_close_document(Decorations.close_document))

      language_client.on_ready().map(_ =>
        language_client.on_notification(LSP.Decoration.name,
          { case LSP.Decoration(decoration) => Decorations.apply_decoration(decoration) }))


      /* super-/subscript decorations */

      Script_Decorations.register_script_decorations(context)


      /* document view ranges */

      def update_document_ranges(editor: Text_Editor): Unit = {
        val uri = editor.document.uri
        val ranges =
          for {
            editor <- Window.visible_editors if editor.document.uri == uri
            range <- editor.visible
          } yield range

        language_client.send_notification(LSP.Document_Ranges_Update(uri.toString, ranges))
      }

      def update_visible_editors(editors: List[Text_Editor]): Unit = {
        last_visible_editors.filterNot(editors.contains).foreach(update_document_ranges)
        editors.filterNot(last_visible_editors.contains).foreach(update_document_ranges)
        last_visible_editors = editors
      }


      /* caret handling */

      def update_caret(): Unit = {
        var caret_update: Option[LSP.Caret_Update] = None
        Window.active_editor.foreach { editor =>
          val uri = editor.document.uri
          val cursor = editor.selection.active
          if (uri.is_file) {
            caret_update = Some(LSP.Caret_Update(uri.toString, cursor))
          }
        }
        if (last_caret_update != caret_update) {
          if (caret_update.isDefined) {
            language_client.send_notification(caret_update.get.json)
          }
          last_caret_update = caret_update
        }
      }

      def goto_file(caret_update: LSP.Caret_Update): Unit = {
        val pos = caret_update.pos

        def show_position(editor: Text_Editor): Unit = editor.reveal(Line.Range(pos))

        def show_file(uri: Uri): Unit =
          Workspace.open_document(uri).map { document =>
            val editor = VSCode_Lib.find_file_editor(document.uri)
            val column = editor.flatMap(_.column) getOrElse Text_Editor.Column.one
            val options =
              Text_Editor.Show_Options(
                column = Some(column),
                preserve_focus = !caret_update.focus,
                selection = Some(Line.Range(pos)))
            Window.show_document(document, options).map(show_position)
          }

        val uri = Uri.parse(caret_update.uri)
        Workspace.is_file(uri).map {
          case true => show_file(uri)
          case false => show_file(uri.copy(scheme = "untitled"))
        }
      }

      language_client.on_ready().map { _ =>
        context.subscribe(
          Window.on_change_active_editor(_ => update_caret()),
          Window.on_change_selection(_ => update_caret()),
          Window.on_change_visible_ranges(update_document_ranges),
          Window.on_change_visible_editors(update_visible_editors))
        update_caret()
        update_visible_editors(Window.visible_editors)

        language_client.on_notification(LSP.Caret_Update.name,
          { case LSP.Caret_Update(Some(caret_update)) => goto_file(caret_update) })
      }


      /* edits */

      def apply_edit(msg: LSP.Document_Edit): Unit = {
        val edit = LSP.TextDocumentEdit(msg.uri, msg.version, List(msg.edit))

        Workspace.edit(edit).map(_ =>
          goto_file(LSP.Caret_Update(msg.uri, msg.end_pos, focus = true)))
      }

      language_client.on_ready().map(_ =>
        language_client.on_notification(LSP.Document_Edit.name,
          { case LSP.Document_Edit(edit) => apply_edit(edit) }))


      /* output view */

      val output_provider = new Output_View.Provider(context, language_client)
      context.subscribe(Window.register(output_provider))

      language_client.on_ready().map(_ =>
        language_client.on_notification(LSP.Dynamic_Output.name,
          { case LSP.Dynamic_Output(content, _) => output_provider.update_content(content) }))


      /* documentation treeview */

      val documentation_provider = new Documentation_Treeview.Provider
      context.subscribe(
        Window.create_treeview(Documentation_Treeview.name, documentation_provider),
        Commands.register(Documentation_Treeview.open_document_command,
          { case uri: Uri => documentation_provider.open_document(uri) }))

      language_client.on_ready().map(_ => documentation_provider.setup(language_client))


      /* symbols view */

      val symbols_provider = new Symbols_View.Provider(context, language_client)
      context.subscribe(Window.register(symbols_provider))

      language_client.on_ready().map(_ => symbols_provider.setup())


      /* sledgehammer view */

      val sledgehammer_provider = new Sledgehammer_View.Provider(context, language_client)
      context.subscribe(Window.register(sledgehammer_provider))

      language_client.on_ready().map(_ => sledgehammer_provider.setup())


      /* state panel */

      context.subscribe(Commands.register("isabelle.state", _ => State_Panel.init()))

      language_client.on_ready().map(_ => State_Panel.setup(context, language_client))


      /* preview panel */

      context.subscribe(
        Commands.register("isabelle.preview", Preview_Panel.request(_, split = false)),
        Commands.register("isabelle.preview-split", Preview_Panel.request(_, split = true)))

      language_client.on_ready().map(_ => Preview_Panel.setup(language_client))


      /* spell checker */

      language_client.on_ready().map { _ =>
        context.subscribe(
          Commands.register("isabelle.include-word", _ =>
            language_client.send_notification(LSP.Include_Word())),
          Commands.register("isabelle.include-word-permanently", _ =>
            language_client.send_notification(LSP.Include_Word_Permanently())),
          Commands.register("isabelle.exclude-word", _ =>
            language_client.send_notification(LSP.Exclude_Word())),
          Commands.register("isabelle.exclude-word-permanently", _ =>
            language_client.send_notification(LSP.Exclude_Word_Permanently())),
          Commands.register("isabelle.reset-words", _ =>
            language_client.send_notification(LSP.Reset_Words())))
      }


      /* start server */

      context.subscribe(language_client.start())
    }
    catch { case exn: Throwable => Window.show_error(Exn.message(exn)) }
  }

  @js.annotation.JSExportTopLevel("deactivate")
  def deactivate(): Unit = {}
}
