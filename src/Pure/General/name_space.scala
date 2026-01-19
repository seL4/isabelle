/*  Title:      Pure/General/name_space.scala
    Author:     Makarius

Isabelle name space entries.
*/

package isabelle

object Name_Space {
  sealed case class Entry(properties: Properties.T) {
    def name: String = Markup.Name.get(properties)
    def kind: String = Markup.Kind.get(properties)

    def gui_name: GUI.Name = GUI.Name(name, kind = kind)
    def print: String = gui_name.toString
    def print_xml: XML.Elem = XML.Elem(Markup.Entity(this), XML.string(print))
  }
}
