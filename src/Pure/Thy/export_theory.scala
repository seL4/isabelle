/*  Title:      Pure/Thy/export_theory.scala
    Author:     Makarius

Export foundational theory content.
*/

package isabelle


object Export_Theory
{
  /* entities */

  sealed case class Entity(name: String, serial: Long, pos: Position.T)
  {
    override def toString: String = name
  }

  def decode_entity(tree: XML.Tree): (Entity, XML.Body) =
  {
    def err(): Nothing = throw new XML.XML_Body(List(tree))

    tree match {
      case XML.Elem(Markup(Markup.ENTITY, props), body) =>
        val name = Markup.Name.unapply(props) getOrElse err()
        val serial = Markup.Serial.unapply(props) getOrElse err()
        val pos = props.filter({ case (a, _) => Markup.POSITION_PROPERTIES(a) })
        (Entity(name, serial, pos), body)
      case _ => err()
    }
  }


  /* types */

  sealed case class Type(entity: Entity, args: List[String], abbrev: Option[Term.Typ])
  {
    def arity: Int = args.length
  }

  def decode_type(tree: XML.Tree): Type =
  {
    val (entity, body) = decode_entity(tree)
    val (args, abbrev) =
    {
      import XML.Decode._
      pair(list(string), option(Term_XML.Decode.typ))(body)
    }
    Type(entity, args, abbrev)
  }


  /* consts */

  sealed case class Const(entity: Entity, typ: Term.Typ, abbrev: Option[Term.Term])

  def decode_const(tree: XML.Tree): Const =
  {
    val (entity, body) = decode_entity(tree)
    val (typ, abbrev) =
    {
      import XML.Decode._
      pair(Term_XML.Decode.typ, option(Term_XML.Decode.term))(body)
    }
    Const(entity, typ, abbrev)
  }
}
