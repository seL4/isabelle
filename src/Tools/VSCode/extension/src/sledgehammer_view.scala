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

  object isar_proofs_clicked extends Scalajs.Fun[Boolean] {
    def apply(state: Boolean): Unit = handle_isar_proofs(state)
  }
  object try0_clicked extends Scalajs.Fun[Boolean] {
    def apply(state: Boolean): Unit = handle_try0(state)
  }
  object apply_query_clicked extends Scalajs.Fun_Unit {
    def apply(): Unit = handle_apply_query()
  }

  private val vscode = Webview_Api.acquire


  /* gui state */

  private var state: State = State()
  private var current_status: String = ""

  object State {
    def unapply(json: JSON.Object.T): Option[State] =
      for {
        provers0 <- JSON.string(json, "provers0")
        case History_Text_Field.State(provers) <- JSON.value(json, "provers")
        isar_proofs <- JSON.bool(json, "isar_proofs")
        try0 <- JSON.bool(json, "try0")
      } yield State(provers0 = provers0, provers = provers, isar_proofs = isar_proofs, try0 = try0)

    def load(): Unit = {
      for { case State(state) <- vscode.get_state } {
        view.state = state
      }
    }

    def save(): Unit =
      vscode.set_state(Some(state.json))
  }

  case class State (
    provers0: String = "",
    provers: History_Text_Field.State = History_Text_Field.State.init(),
    isar_proofs: Boolean = false,
    try0: Boolean = false,
  ) {
    def json: JSON.Object.T =
      JSON.Object(
        "provers0" -> provers0,
        "provers" -> provers.json,
        "isar_proofs" -> isar_proofs,
        "try0" -> try0)
  }


  /* query operation */

  private def process_indicator: XML.Elem = {
    if (current_status == "" || current_status == "Finished") HTML.span(Nil)
    else VSCode_Elements.spinner
  }


  /* controls */

  def handle_provers_update(provers_update: History_Text_Field.Update): Unit = {
    update(state.copy(provers = provers_update.state))
    if (provers_update.submit) {
      vscode.post(LSP.Sledgehammer_Request(state.provers.input, state.isar_proofs, state.try0))
    }
  }
  private def provers_text_field: History_Text_Field =
    History_Text_Field("provers", handle_provers_update, state.provers, columns = 30,
      tooltip = "Automatic provers as space-separated list", placeholder = state.provers0)
  private val provers_label = VSCode_Elements.label("Provers:", "provers")

  def handle_isar_proofs(state: Boolean): Unit = update(view.state.copy(isar_proofs = state))
  private def isar_proofs_checkbox: XML.Elem =
    VSCode_Elements.checkbox("Isar proofs",
      tooltip = "Specify whether Isar proofs should be output in addition to \"by\" one-liner",
      selected = state.isar_proofs, script = isar_proofs_clicked.function("this.checked"))

  def handle_try0(state: Boolean): Unit = update(view.state.copy(try0 = state))
  private def try0_checkbox =
    VSCode_Elements.checkbox("Try methods",
      tooltip = "Try standard proof methods like \"auto\" and \"blast\" as alternatives to \"metis\"",
      selected = state.try0, script = try0_clicked.function("this.checked"))

  def handle_apply_query(): Unit = provers_text_field.submit()
  private def apply_query: XML.Elem = {
    VSCode_Elements.button("Apply",
      tooltip = "Search for first-order proof using automatic theorem provers",
      script = apply_query_clicked.function())
  }

  private val cancel_query =
    VSCode_Elements.button("Cancel", secondary = true,
      tooltip = "Interrupt unfinished sledgehammering",
      script = Webview_Api.Post.function(JSON.Format(LSP.Sledgehammer_Cancel())))

  private val locate_query =
    VSCode_Elements.button("Locate", secondary = true,
      tooltip = "Locate context of current query within source text",
      script = Webview_Api.Post.function(JSON.Format(LSP.Sledgehammer_Locate())))

  private def controls: XML.Elem =
    HTML.Wrap_Panel(
      List(provers_label, provers_text_field.html, isar_proofs_checkbox, try0_checkbox,
        process_indicator, apply_query, cancel_query, locate_query))


  /* output text area */

  private val pretty_text_area = new Pretty_Text_Area(_ => update(state))


  /* main */

  def update(state: State): Unit = {
    if (view.state != state) {
      view.state = state
      State.save()
    }
    Scalajs.DOM.update(HTML.control_markup(controls :: pretty_text_area.html, hidden = true))
  }

  def main(): Unit = {
    State.load()

    Webview_Api.on_message { e =>
      val json = Scalajs.JSON.unapply(e.data).get

      JSON.string(json, "command") match {
        case Some("status") =>
          current_status = JSON.string(json, "message").get
          update(state)
        case Some("provers") =>
          update(state.copy(provers0 = JSON.string(json, "provers").get))
        case Some("result") =>
          val content = YXML.parse_body(YXML.Source(JSON.string(json, "content").get))
          pretty_text_area.handle_update(content)
        case _ =>
      }
    }

    pretty_text_area.init()
    vscode.post(JSON.Object("command" -> "ready"))
    update(state)
  }
}
