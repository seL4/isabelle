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

  def document_editor_session: Option[Sessions.Background] =
    document_editor.value.session_background
  def document_editor_active: Boolean =
    document_editor.value.is_active
  def document_editor_setup(background: Option[Sessions.Background]): Unit =
    document_editor.change(_.copy(session_background = background))
  def document_editor_init(id: AnyRef): Unit =
    document_editor.change(_.register_view(id))
  def document_editor_exit(id: AnyRef): Unit =
    document_editor.change(_.unregister_view(id))


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
