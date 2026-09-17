/*  Title:      Tools/VSCode/extension/history_text_field.scala
    Author:     Fabian Huch

VSCode component for text fields with history.
*/

package isabelle.vscode.extension

import org.scalajs.dom

import isabelle._


object History_Text_Field {
  private var instances: Map[String, History_Text_Field] = Map.empty

  object input extends Scalajs.Fun2[String, String] {
    def apply(name: String, s: String): Unit = instances(name).handle_input(s)
  }
  object focused extends Scalajs.Fun2[String, Boolean] {
    def apply(name: String, state: Boolean): Unit = instances(name).handle_focus(state)
  }
  object key_down extends Scalajs.Fun2[String, dom.KeyboardEvent] {
    def apply(name: String, event: dom.KeyboardEvent): Unit =
      instances(name).handle_key_event(event)
  }


  /* history items */

  object Item {
    object clicked extends Scalajs.Fun2[String, Int] {
      def apply(name: String, index: Int): Unit = instances(name).handle_select(index)
    }
    object remove_clicked extends Scalajs.Fun3[String, Int, dom.MouseEvent] {
      def apply(name: String, index: Int, event: dom.MouseEvent): Unit = {
        event.stopPropagation()
        instances(name).handle_remove(index)
      }
    }
  }

  case class Item(value: String, index: Int, focused: Boolean) {
    def html(name: String): XML.Elem = {
      val remove_button =
        HTML.GUI.onclick(Item.remove_clicked.function(JS.string(name), JS.int(index), "event"))(
          HTML.span("history-entry-remove", HTML.text("\u2716")))

      val content = HTML.text(value) ::: remove_button :: Nil

      HTML.GUI.onclick(Item.clicked.function(JS.string(name), JS.int(index)))(
        HTML.div(if_proper(focused, "active ") + "history-entry", content))
    }
  }


  /* GUI state */

  object State {
    def init(input: String = "", history: List[String] = Nil): State = new State(input, history)

    def unapply(json: JSON.T): Option[State] =
      for {
        input <- JSON.string(json, "input")
        history <- JSON.strings(json, "history")
      } yield init(input, history)
  }

  class State private(
    val input: String,
    private val history: List[String],
    val focused: Boolean = false,
    private val item_focus: Int = -1
  ) {
    state =>

    override def toString: String = "History_Text_Field.State(" + input + ")"
    override def hashCode(): Int = (input, history, focused, item_focus).hashCode()
    override def equals(other: Any): Boolean =
      other match {
        case that: State =>
          that.input == input && that.history == history && that.focused == focused &&
            that.item_focus == item_focus
        case _ => false
      }

    def json: JSON.T = JSON.Object("input" -> input, "history" -> history)
    def item_focused: Boolean = item_focus > -1
    def history_items: List[Item] =
      history.zipWithIndex.map((item, index) => Item(item, index, index == item_focus))

    private def copy(
      input: String = input, history: List[String] = history, focused: Boolean = focused,
        item_focus: Int = item_focus): State =
      new State(input, history, focused, item_focus)

    def reset_item_focus: State = copy(item_focus = -1)
    def reset_focus: State = reset_item_focus.copy(focused = false)
    def update_input(input: String): State = reset_item_focus.copy(input = input)

    def update_focus(focused: Boolean): State = reset_focus.copy(focused = focused)
    def add_entry: State =
      reset_item_focus.copy(history = if (input.isEmpty) history else (input :: history).distinct)

    def wrap_index(n: Int, index: Int): Int =
      if (n < 1) -1 else if (index < 0) n - 1 else if (index >= n) 0 else index

    def next_entry(rev: Boolean = false): State =
      copy(focused = true, item_focus =
        wrap_index(history.length, item_focus + (if (rev) -1 else 1)))

    private def get(index: Int): Option[String] =
      if (index >= 0 && index < history.length) Some(history(index)) else None

    def select_focused: State = select(item_focus)
    def select(index: Int): State =
      get(index) match { case None => state case Some(s) => reset_item_focus.copy(input = s) }

    def remove(index: Int): State =
      get(index) match {
        case None => state
        case Some(s) =>
          val history1 = Library.remove(s)(history)
          val item_focus1 =
            if (item_focus > 0 && index <= item_focus) wrap_index(history1.length, item_focus - 1)
            else item_focus
          copy(history = history1, item_focus = item_focus1)
      }
  }


  /* component update */

  case class Update(state: State, submit: Boolean)

  def apply(
    name: String,
    on_update: Update => Unit,
    state: State = State.init(),
    columns: Int = 0,
    tooltip: String = "",
  ): History_Text_Field = {
    val text_field = new History_Text_Field(name, columns, tooltip, state, on_update)
    instances += name -> text_field
    text_field
  }
}

class History_Text_Field private(
  name: String,
  columns: Int,
  tooltip: String,
  state: History_Text_Field.State,
  on_update: History_Text_Field.Update => Unit,
) {
  history_text_field =>

  private def update(state: History_Text_Field.State, submit: Boolean = false): Unit =
    if (submit || history_text_field.state != state) {
      on_update(History_Text_Field.Update(state, submit))
    }

  def submit(): Unit = update(state.add_entry, submit = true)

  def handle_input(s: String): Unit = update(state.update_input(s))
  def handle_focus(focused: Boolean): Unit = update(state.update_focus(focused))
  def handle_select(index: Int): Unit = update(state.select(index))
  def handle_remove(index: Int): Unit = update(state.remove(index))
  def handle_key_event(e: dom.KeyboardEvent): Unit =
    if (!e.isComposing) {
      e.keyCode match {
        case dom.KeyCode.Enter  =>
          e.preventDefault()
          if (state.item_focused) update(state.select_focused) else submit()
        case dom.KeyCode.Down =>
          e.preventDefault()
          update(state.next_entry())
        case dom.KeyCode.Up =>
          e.preventDefault()
          update(state.next_entry(rev = true))
        case dom.KeyCode.Escape =>
          e.currentTarget.asInstanceOf[dom.HTMLElement].blur()
        case _ =>
      }
    }

  def html: XML.Elem = {
    val input_field = 
      HTML.GUI.onfocus(History_Text_Field.focused.function(JS.string(name), JS.boolean(true)))(
        HTML.GUI.onkeydown(History_Text_Field.key_down.function(JS.string(name), "event"))(
          HTML.GUI.text_field(columns = columns, text = state.input, name = name, tooltip = tooltip,
            script = History_Text_Field.input.function(JS.string(name), "this.value"))))

    val drop_down =
      if (!state.focused) Nil
      else {
        val entries =
          HTML.div("history-entry", HTML.text("Previously entered strings:")) ::
            state.history_items.map(_.html(name))
        List(HTML.GUI.onmousedown("event.preventDefault()")(HTML.div("history-dropdown", entries)))
      }

    HTML.GUI.onfocusout(History_Text_Field.focused.function(JS.string(name), JS.boolean(false)))(
      HTML.div("history-text-field", input_field :: drop_down))
  }
}
