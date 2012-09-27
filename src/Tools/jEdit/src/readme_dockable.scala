/*  Title:      Tools/jEdit/src/readme_dockable.scala
    Author:     Makarius

Dockable window for README.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.View


class README_Dockable(view: View, position: String) extends Dockable(view, position)
{
  Swing_Thread.require()

  private val readme = new HTML_Panel
  private val readme_path = Path.explode("$JEDIT_HOME/README.html")
  readme.render_document(Isabelle_System.platform_file_url(readme_path), File.read(readme_path))

  set_content(readme)
}
