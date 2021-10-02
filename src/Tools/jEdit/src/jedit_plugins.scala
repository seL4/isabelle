/*  Title:      Tools/jEdit/src/jedit_plugin.scala
    Author:     Makarius

Isabelle/jEdit plugins via dynamic Isabelle/Scala/Java modules.
*/

package isabelle.jedit

import isabelle._


class JEdit_Plugin0 extends
  Scala_Project.Plugin(Path.explode("$ISABELLE_HOME/src/Tools/jEdit/jedit_base"))

class JEdit_Plugin1 extends
  Scala_Project.Plugin(Path.explode("$ISABELLE_HOME/src/Tools/jEdit/jedit_main"))
