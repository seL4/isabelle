/*  Title:      Tools/Find_Facts/src/find_facts_tools.scala
    Author:     Fabian Huch, TU Muenchen

JVM entry points for command-line tools in $FIND_FACTS_HOME/Tools/.
*/

package isabelle.find_facts

object Find_Facts_Index_Tool { def main(args: Array[String]): Unit = Find_Facts.main_tool1(args) }
object Find_Facts_Tool { def main(args: Array[String]): Unit = Find_Facts.main_tool3(args) }
