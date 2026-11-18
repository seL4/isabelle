/*  Title:      Tools/VSCode/extension/src/vscode_lib.scala
    Author:     Makarius
    Author:     Fabian Huch

Misc library functions for VSCode.
*/

package isabelle.vscode.extension

import VSCode.{Text_Editor, Uri, Window, Workspace}

import isabelle._


object VSCode_Lib {
  val file_scheme = "file"

  /* files */

  def find_file_editor(uri: Uri): Option[Text_Editor] = {
    def check(editor: Text_Editor): Boolean =
      editor.document.uri.is_file && editor.document.uri.platform_path == uri.platform_path

    if (uri.is_file) Window.active_editor.filter(check).orElse(Window.visible_editors.find(check))
    else None
  }


  /* GUI */

  def adjacent_editor_column(editor: Option[Text_Editor], split: Boolean): Text_Editor.Column =
    editor.flatMap(_.column) match {
      case None => Text_Editor.Column.one
      case Some(column) =>
        if (!split) column
        else if (column == Text_Editor.Column.one || column == Text_Editor.Column.three)
          Text_Editor.Column.two
        else Text_Editor.Column.three
    }


  /* Isabelle configuration */

  def get_configuration(name: String): Option[JSON.T] =
    Workspace.configuration("isabelle").get(name)

  def set_configuration(name: String, value: JSON.T): Unit =
    Workspace.configuration("isabelle").update(name, value)

  def get_replacement_mode(): String =
    get_configuration("replacement").collect {
      case s: String if List("none", "non-alphanumeric", "all").contains(s) => s
    }.get

  def get_color(color: String, light: Boolean): String = {
    val colors = get_configuration("text_color").get
    JSON.string(colors, color + (if (light) "_light" else "_dark")).get
  }
}
