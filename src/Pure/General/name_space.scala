/*  Title:      Pure/General/name_space.scala
    Author:     Makarius

Isabelle name space entries.
*/

package isabelle

object Name_Space {
  sealed case class Entry(properties: Properties.T) {
    def name: String = Markup.Name.get(properties)
    def kind: String = Markup.Kind.get(properties)
    def def_label: String = Position.Def_Label.get(properties)

    def print(style: GUI.Style = GUI.Style_Plain): String =
      GUI.Name(name, kind = Word.informal(kind), prefix = def_label, style = style).toString
    def print_xml(style: GUI.Style = GUI.Style_Plain): XML.Elem =
      XML.Elem(Markup.Entity(this), XML.string(print(style = style)))
  }
}
