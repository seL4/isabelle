/*  Title:      Tools/VSCode/src/vscode_session.scala
    Author:     Makarius

PIDE editor session for Isabelle/VSCode.
*/

package isabelle.vscode


import isabelle._


class VSCode_Session(
  _session_options: => Options,
  _resources: VSCode_Resources
) extends Session {
  override def session_options: Options = _session_options
  override def resources: VSCode_Resources = _resources
}
