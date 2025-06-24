/*  Title:      Tools/jEdit/src/jedit_session.scala
    Author:     Makarius

PIDE editor session for Isabelle/jEdit.
*/

package isabelle.jedit


import isabelle._


class JEdit_Session(_session_options: => Options) extends Session(_session_options) {
  override val resources: JEdit_Resources = JEdit_Resources(_session_options)
}
