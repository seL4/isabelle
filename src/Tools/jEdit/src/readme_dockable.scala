/*  Title:      Tools/jEdit/src/readme_dockable.scala
    Author:     Makarius

Dockable window for README.
*/

package isabelle.jedit


import isabelle._

import org.gjt.sp.jedit.View


class README_Dockable(view: View, position: String) extends Dockable(view: View, position: String)
{
  private val readme = new HTML_Panel("SansSerif", 14)
  private val readme_path = Path.explode("$JEDIT_HOME/README.html")
  readme.render_document(
    Isabelle_System.platform_file_url(readme_path),
    Isabelle_System.try_read(List(readme_path)))

  set_content(readme)
}
