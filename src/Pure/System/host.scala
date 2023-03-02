/*  Title:      Pure/System/host.scala
    Author:     Makarius

Information about compute hosts.
*/

package isabelle


object Host {
  /* allocated resources */

  object Node_Info { def none: Node_Info = Node_Info("", None) }

  sealed case class Node_Info(hostname: String, numa_node: Option[Int])
}
