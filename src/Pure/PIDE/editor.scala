/*  Title:      Pure/PIDE/editor.scala
    Author:     Makarius

General editor operations.
*/

package isabelle


abstract class Editor[Context]
{
  def session: Session
  def flush(): Unit
  def current_context: Context
  def current_node(context: Context): Option[Document.Node.Name]
  def current_snapshot(context: Context): Option[Document.Snapshot]
  def node_snapshot(name: Document.Node.Name): Document.Snapshot
  def current_command(context: Context, snapshot: Document.Snapshot): Option[(Command, Text.Offset)]

  def node_overlays(name: Document.Node.Name): Document.Node.Overlays
  def insert_overlay(command: Command, fn: String, args: List[String]): Unit
  def remove_overlay(command: Command, fn: String, args: List[String]): Unit
}

