/*  Title:      Pure/PIDE/editor.scala
    Author:     Makarius

General editor operations.
*/

package isabelle


abstract class Editor[Context]
{
  /* session */

  def session: Session
  def flush(): Unit
  def invoke(): Unit


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

  abstract class Hyperlink
  {
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
