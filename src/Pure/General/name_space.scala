/*  Title:      Pure/General/name_space.scala
    Author:     Makarius

Isabelle name space entries.
*/

package isabelle

object Name_Space {
  sealed case class Entry(props: Properties.T) {
    def name: String = Markup.Name.get(props)
    def kind: String = Markup.Kind.get(props)
    def gui_name: GUI.Name = GUI.Name(name, kind = kind)
    override def toString: String = gui_name.toString
  }
}
