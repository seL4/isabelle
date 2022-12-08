/*  Title:      Pure/PIDE/document_editor.scala
    Author:     Makarius

Central resources for interactive document preparation.
*/

package isabelle


object Document_Editor {
  /* document output */

  def document_name: String = "document"
  def document_output_dir(): Path = Path.explode("$ISABELLE_HOME_USER/document_output")
  def document_output(): Path = document_output_dir() + Path.basic(document_name)

  def view_document(): Unit = {
    val path = document_output().pdf
    if (path.is_file) Isabelle_System.pdf_viewer(path)
  }


  /* progress */

  class Log_Progress(session: Session) extends Progress {
    def show(text: String): Unit = {}

    private val syslog = session.make_syslog()

    private def update(text: String = syslog.content()): Unit = show(text)
    private val delay =
      Delay.first(session.session_options.seconds("editor_update_delay"), gui = true) { update() }

    override def echo(msg: String): Unit = { syslog += msg; delay.invoke() }

    def load(): Unit = GUI_Thread.require {
      val path = document_output().log
      val text = if (path.is_file) File.read(path) else ""
      GUI_Thread.later { delay.revoke(); update(text) }
    }

    GUI_Thread.later { update() }
  }
}
