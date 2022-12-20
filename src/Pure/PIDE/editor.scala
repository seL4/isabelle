/*  Title:      Pure/PIDE/editor.scala
    Author:     Makarius

General editor operations.
*/

package isabelle


abstract class Editor[Context] {
  /* session */

  def session: Session
  def flush(): Unit
  def invoke(): Unit


  /* document editor */

  protected val document_editor: Synchronized[Document_Editor.State] =
    Synchronized(Document_Editor.State())

  protected def document_state(): Document_Editor.State = document_editor.value

  protected def document_state_changed(): Unit = {}
  private def document_state_change(f: Document_Editor.State => Document_Editor.State): Unit = {
    val changed =
      document_editor.change_result { st =>
        val st1 = f(st)
        (st.required != st1.required, st1)
      }
    if (changed) document_state_changed()
  }

  def document_session(): Option[Sessions.Background] = document_state().session_background
  def document_required(): List[Document.Node.Name] = document_state().required
  def document_node_required(name: Document.Node.Name): Boolean = document_state().is_required(name)

  def document_theories(): List[Document.Node.Name] = document_state().active_document_theories

  def document_setup(background: Option[Sessions.Background]): Unit =
    document_state_change(_.copy(session_background = background))

  def document_select(
    names: Iterable[Document.Node.Name],
    set: Boolean = false,
    toggle: Boolean = false
  ): Unit = document_state_change(_.select(names, set = set, toggle = toggle))

  def document_select_all(set: Boolean = false): Unit =
    document_state_change(st => st.select(st.active_document_theories, set = set))

  def document_init(id: AnyRef): Unit = document_state_change(_.register_view(id))
  def document_exit(id: AnyRef): Unit = document_state_change(_.unregister_view(id))


  /* current situation */

  def current_node(context: Context): Option[Document.Node.Name]
  def current_node_snapshot(context: Context): Option[Document.Snapshot]
  def node_snapshot(name: Document.Node.Name): Document.Snapshot
  def current_command(context: Context, snapshot: Document.Snapshot): Option[Command]


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
