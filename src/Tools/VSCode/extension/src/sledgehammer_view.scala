/*  Title:      Tools/VSCode/extension/sledgehammer_view.scala
    Author:     Fabian Huch

Sledgehammer view within Isabelle/VSCode extension.
*/

package isabelle.vscode.extension

import isabelle._
import isabelle.vscode._

import org.scalajs.dom


object Sledgehammer_View {
  view =>

  private val vscode = Webview_Api.acquire


  /* gui state */

  private var provers0: String = ""
  private var current_status: String = ""
  private var provers: History_Text_Field.State = History_Text_Field.State.init()
  private var isar_proofs: Boolean = false
  private var try0: Boolean = true

  object State {
    def apply(
      provers0: String,
      provers: History_Text_Field.State,
      isar_proofs: Boolean,
      try0: Boolean
    ): JSON.Object.T =
      JSON.Object(
        "provers0" -> provers0,
        "provers" -> provers.json,
        "isar_proofs" -> isar_proofs,
        "try0" -> try0)

    def unapply(json: JSON.Object.T): Option[(String, History_Text_Field.State, Boolean, Boolean)] =
      for {
        provers0 <- JSON.string(json, "provers0")
        case History_Text_Field.State(provers) <- JSON.value(json, "provers")
        isar_proofs <- JSON.bool(json, "isar_proofs")
        try0 <- JSON.bool(json, "try0")
      } yield (provers0, provers, isar_proofs, try0)

    def load(): Unit = {
      for (case State(provers0, provers, isar_proofs, try0) <- vscode.get_state) {
        view.provers0 = provers0
        view.provers = provers
        view.isar_proofs = isar_proofs
        view.try0 = try0
      }
    }

    def save(): Unit =
      vscode.set_state(Some(State(provers0, provers, isar_proofs, try0)))
  }


  /* query operation */

  private def process_indicator: XML.Elem = {
    val elem =
      if (current_status == "" || current_status == "Finished") HTML.div(Nil)
      else HTML.div("loading", Nil)
    HTML.id("sledgehammer-spinner")(elem)
  }


  /* controls */

  private def update_provers(provers_update: History_Text_Field.Update): Unit = {
    provers = provers_update.state
    if (provers_update.submit) {
      State.save()
      vscode.post(LSP.Sledgehammer_Request(provers.input, isar_proofs, try0))
    }
    else update()
  }
  private def provers_text_field: History_Text_Field =
    History_Text_Field("provers", update_provers, provers, columns = 30,
      tooltip = "Automatic provers as space-separated list, e.g.\n" + provers0)
  private val provers_label = HTML.GUI.label("Provers:", "provers")

  object isar_proofs_checkbox_clicked extends Scalajs.Fun[Boolean] {
    def apply(state: Boolean): Unit = { isar_proofs = state }
  }
  private def isar_proofs_checkbox: XML.Elem =
    HTML.GUI.checkbox(HTML.text("Isar proofs"),
      tooltip = "Specify whether Isar proofs should be output in addition to \"by\" one-liner",
      selected = isar_proofs, script = isar_proofs_checkbox_clicked.function("this.checked"))

  object try0_checkbox_clicked extends Scalajs.Fun[Boolean] {
    def apply(state: Boolean): Unit = { try0 = state }
  }
  private def try0_checkbox =
    HTML.GUI.checkbox(HTML.text("Try methods"),
      tooltip = "Try standard proof methods like \"auto\" and \"blast\" as alternatives to \"metis\"",
      selected = try0, script = try0_checkbox_clicked.function("this.checked"))

  object apply_query_clicked extends Scalajs.Fun_Unit {
    def apply(): Unit = provers_text_field.submit()
  }
  private def apply_query: XML.Elem = {
    HTML.GUI.button(List(HTML.bold(HTML.text("Apply"))),
      tooltip = "Search for first-order proof using automatic theorem provers",
      script = apply_query_clicked.function())
  }

  private val cancel_query =
    HTML.GUI.button(HTML.text("Cancel"),
      tooltip = "Interrupt unfinished sledgehammering",
      script = Webview_Api.Post.function(JSON.Format(LSP.Sledgehammer_Cancel())))

  private val locate_query =
    HTML.GUI.button(HTML.text("Locate"),
      tooltip = "Locate context of current query within source text",
      script = Webview_Api.Post.function(JSON.Format(LSP.Sledgehammer_Locate())))

  private def controls: XML.Elem =
    HTML.Wrap_Panel(
      List(provers_label, provers_text_field.html, isar_proofs_checkbox, try0_checkbox,
        process_indicator, apply_query, cancel_query, locate_query))


  /* output text area */

  private var current_output: XML.Body = Nil


  /* main */

  def update(): Unit = {
    State.save()
    Scalajs.DOM.update(HTML.control_markup(controls :: current_output, hidden = true))
  }

  def main(): Unit = {
    State.load()

    Pretty_Text_View.on_update { output =>
      current_output = output
      update()
    }

    dom.window.onresize = { _ => Pretty_Text_View.on_resize() }
    dom.window.onload = { _ => Pretty_Text_View.on_load() }

    Webview_Api.on_message { e =>
      val json = Scalajs.JSON.unapply(e.data).get

      JSON.string(json, "command") match {
        case Some("status") =>
          current_status = JSON.string(json, "message").get
          update()
        case Some("provers") =>
          provers0 = JSON.string(json, "provers").get
          update()
        case Some("result") =>
          val output = YXML.parse_body(YXML.Source(JSON.string(json, "content").get))
          
          Pretty_Text_View.handle_update(output)
        case _ =>
      }
    }

    vscode.post(JSON.Object("command" -> "ready"))
    update()
  }
}
