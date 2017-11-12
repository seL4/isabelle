/*  Title:      Pure/Thy/thy_resources.scala
    Author:     Makarius

PIDE resources for theory files.
*/

package isabelle


object Thy_Resources
{
  /* internal state */

  sealed case class State(
    models: Map[Document.Node.Name, Thy_Document_Model] = Map.empty)
}

class Thy_Resources(
    val options: Options,
    session_base: Sessions.Base,
    log: Logger = No_Logger)
  extends Resources(session_base, log = log)
{
  private val state = Synchronized(Thy_Resources.State())
}
