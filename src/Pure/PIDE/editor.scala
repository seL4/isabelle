/*  Title:      Pure/PIDE/editor.scala
    Author:     Makarius

General editor operations.
*/

package isabelle


object Editor {
  /* output messages */

  object Output {
    val none: Output = Output(defined = false)
    val init: Output = Output()
  }

  sealed case class Output(
    results: Command.Results = Command.Results.empty,
    messages: List[XML.Elem] = Nil,
    defined: Boolean = true
  )
}

abstract class Editor[Context] {
  /* PIDE session and document model */

  def session: Session
  def flush(): Unit
  def invoke(): Unit

  def get_models(): Iterable[Document.Model]


  /* document editor */

  protected val document_editor: Synchronized[Document_Editor.State] =
    Synchronized(Document_Editor.State())

  protected def document_state(): Document_Editor.State = document_editor.value

  protected def document_state_changed(): Unit = {}
  private def document_state_change(f: Document_Editor.State => Document_Editor.State): Unit = {
    val changed =
      document_editor.change_result { st =>
        val st1 = f(st)
        val changed =
          st.active_document_theories != st1.active_document_theories ||
          st.selection != st1.selection
        (changed, st1)
      }
    if (changed) document_state_changed()
  }

  def document_session(): Document_Editor.Session =
    document_state().session(session)

  def document_required(): List[Document.Node.Name] = {
    val st = document_state()
    if (st.is_active) {
      for {
        a <- st.all_document_theories
        b = session.resources.migrate_name(a)
        if st.selection(b.theory)
      } yield b
    }
    else Nil
  }

  def document_node_required(name: Document.Node.Name): Boolean = {
    val st = document_state()
    st.is_active &&
    st.selection.contains(name.theory) &&
    st.all_document_theories.exists(a => a.theory == name.theory)
  }

  def document_theories(): List[Document.Node.Name] =
    document_state().active_document_theories.map(session.resources.migrate_name)

  def document_selection(): Set[String] = document_state().selection

  def document_setup(background: Option[Sessions.Background]): Unit =
    document_state_change(_.copy(session_background = background))

  def document_select(
    theories: Iterable[String],
    set: Boolean = false,
    toggle: Boolean = false
  ): Unit = document_state_change(_.select(theories, set = set, toggle = toggle))

  def document_select_all(set: Boolean = false): Unit =
    document_state_change(st =>
      st.select(st.active_document_theories.map(_.theory), set = set))

  def document_init(id: AnyRef): Unit = document_state_change(_.register_view(id))
  def document_exit(id: AnyRef): Unit = document_state_change(_.unregister_view(id))


  /* current situation */

  def current_node(context: Context): Option[Document.Node.Name]
  def current_node_snapshot(context: Context): Option[Document.Snapshot]
  def node_snapshot(name: Document.Node.Name): Document.Snapshot
  def current_command(context: Context, snapshot: Document.Snapshot): Option[Command]


  /* output messages */

  def output_state(): Boolean

  def output(
    snapshot: Document.Snapshot,
    offset: Text.Offset,
    restriction: Option[Set[Command]] = None
  ): Editor.Output = {
    if (snapshot.is_outdated) Editor.Output.none
    else {
      snapshot.current_command(snapshot.node_name, offset) match {
        case None => Editor.Output.init
        case Some(command) =>
          if (restriction.isEmpty || restriction.get.contains(command)) {
            val results = snapshot.command_results(command)

            val (states, other) =
              results.iterator.map(_._2).filterNot(Protocol.is_result).toList
                .partition(Protocol.is_state)
            val (urgent, regular) = other.partition(Protocol.is_urgent)
            val messages = urgent ::: (if (output_state()) states else Nil) ::: regular

            Editor.Output(results = results, messages = messages)
          }
          else Editor.Output.none
      }
    }
  }


  /* overlays */

  def node_overlays(name: Document.Node.Name): Document.Node.Overlays
  def insert_overlay(command: Command, fn: String, args: List[String]): Unit
  def remove_overlay(command: Command, fn: String, args: List[String]): Unit


  /* hyperlinks */

  abstract class Hyperlink {
    def external: Boolean = false
    def follow(context: Context): Unit
  }

  def hyperlink_command(
    focus: Boolean, snapshot: Document.Snapshot, id: Document_ID.Generic, offset: Symbol.Offset = 0)
      : Option[Hyperlink]


  /* dispatcher thread */

  def assert_dispatcher[A](body: => A): A
  def require_dispatcher[A](body: => A): A
  def send_dispatcher(body: => Unit): Unit
  def send_wait_dispatcher(body: => Unit): Unit
}
