/*  Title:      Tools/VSCode/extension/vscode_elements.scala
    Author:     Fabian Huch

VSCode GUI elements, based @vscode/codicons icons and CSS from @vscode-elements/elements-lite.
See also:

  - https://microsoft.github.io/vscode-codicons/dist/codicon.html
  - https://vscode-elements.github.io/
*/

package isabelle.vscode.extension

import isabelle._


object VSCode_Elements {
  /* codicons */

  def codicon(icon: String): XML.Elem =
    XML.elem(Markup("i", List("class" -> ("codicon codicon-" + icon), "aria-hidden" -> "true")))

  def spinner: XML.Elem =
    XML.elem(Markup("i", List("class" -> "codicon codicon-loading codicon-modifier-spin",
      "aria-label" -> "Waiting ...")))


  /* elements lite */

  def action_button(icon: String, label: String = "", name: String = "", tooltip: String = "",
      disabled: Boolean = false, script: String = ""): XML.Elem = {
    val content =
      codicon(icon) :: proper_string(label).map(s => HTML.span("label", HTML.text(s))).toList
    val button = HTML.GUI.button(content, name = name, tooltip = tooltip, script = script)
    HTML.class_("vscode-action-button")(if (disabled) button + ("disabled" -> "true") else button)
  }

  def button(text: String, name: String = "", tooltip: String = "", secondary: Boolean = false,
      block: Boolean = false, source: Boolean = false, script: String = ""): XML.Elem = {
    val styles =
      if_proper(secondary, " secondary") + if_proper(block, " block") + if_proper(source, " source")
    HTML.class_("vscode-button" + styles)(
      HTML.GUI.button(HTML.text(text), name = name, tooltip = tooltip, script = script))
  }

  def checkbox(text: String, name: String = "", tooltip: String = "", selected: Boolean = false,
      script: String = ""): XML.Elem = {
    val content =
      List(
        HTML.span("icon", List(codicon("check icon-checked"))), HTML.span("text", HTML.text(text)))

    val elem =
      HTML.div("vscode-checkbox", List(
        HTML.GUI.checkbox(content, name = name, selected = selected, script = script)))
    HTML.GUI.optional_title(tooltip).foldLeft(elem)(_ + _)
  }

  def label(text: String, label_for: String, pale: Boolean = false): XML.Elem =
    XML.Elem(Markup("label", List("class" -> "vscode-label", "for" -> label_for)),
      List(if (pale) HTML.span("pale", HTML.text(text)) else HTML.span(HTML.text(text))))

  def text_field(columns: Int = 0, before: XML.Body = Nil, text: String = "", after: XML.Body = Nil,
      name: String = "", tooltip: String = "", placeholder: String = "", script: String = "")
      : XML.Elem = {
    val text_field =
      HTML.GUI.text_field(columns = columns, text = text, name = name, tooltip = tooltip,
        placeholder = placeholder, script = script)
    HTML.div("vscode-textfield", before ::: text_field :: after)
  }


  /* additional elements */

  def tab_header(text: String, selected: Boolean = false, tooltip: String = "", script: String = "")
      : XML.Elem =
    HTML.class_("vscode-tab-header" + if_proper(selected, " active"))(
      HTML.GUI.button(HTML.text(text), tooltip = tooltip, script = script)) + ("role" -> "tab")

  def tab_panel(body: XML.Body, selected: Boolean = false): XML.Elem = {
    val panel = HTML.div("vscode-tab-panel", body) + ("role" -> "tabpanel")
    if (selected) panel else panel + ("hidden" -> "true")
  }

  def tabs(elems: List[(XML.Elem, XML.Elem)]): XML.Elem =
    HTML.div(HTML.div("vscode-tablist", elems.map(_._1)) + ("role" -> "tablist") :: elems.map(_._2))
}
