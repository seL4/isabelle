/*  Title:      Pure/Thy/export_theory.scala
    Author:     Makarius

Export foundational theory content.
*/

package isabelle


object Export_Theory
{
  /** session content **/

  sealed case class Session(name: String, theory_graph: Graph[String, Theory])
  {
    override def toString: String = name

    def theory(theory_name: String): Theory =
      if (theory_graph.defined(theory_name)) theory_graph.get_node(theory_name)
      else error("Bad theory " + quote(theory_name))

    def theories: List[Theory] =
      theory_graph.topological_order.map(theory_graph.get_node(_))
  }

  def read_session(session_name: String,
    system_mode: Boolean = false,
    types: Boolean = true,
    consts: Boolean = true): Session =
  {
    val store = Sessions.store(system_mode)

    val thys =
      using(SQLite.open_database(store.the_database(session_name)))(db =>
      {
        db.transaction {
          Export.read_theory_names(db, session_name).iterator.map(_._1).toSet.iterator.
            map((theory_name: String) =>
              read_theory(db, session_name, theory_name, types = types, consts = consts)).toList
        }
      })

    val graph0 =
      (Graph.string[Theory] /: thys) { case (g, thy) => g.new_node(thy.name, thy) }
    val graph1 =
      (graph0 /: thys) { case (g0, thy) =>
        (g0 /: thy.parents) { case (g1, parent) =>
          g1.default_node(parent, empty_theory(parent)).add_edge_acyclic(parent, thy.name) } }

    Session(session_name, graph1)
  }



  /** theory content **/

  sealed case class Theory(
    name: String, parents: List[String], types: List[Type], consts: List[Const])
  {
    override def toString: String = name
  }

  def empty_theory(name: String): Theory = Theory(name, Nil, Nil, Nil)

  def read_theory(db: SQL.Database, session_name: String, theory_name: String,
    types: Boolean = true,
    consts: Boolean = true): Theory =
  {
    val parents =
      Export.read_entry(db, session_name, theory_name, "theory/parents") match {
        case Some(entry) =>
          import XML.Decode._
          list(string)(entry.uncompressed_yxml())
        case None =>
          error("Missing theory export in session " + quote(session_name) + ": " +
            quote(theory_name))
      }
    Theory(theory_name, parents,
      if (types) read_types(db, session_name, theory_name) else Nil,
      if (consts) read_consts(db, session_name, theory_name) else Nil)
  }


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

  def read_entities[A](db: SQL.Database, session_name: String, theory_name: String,
    export_name: String, decode: XML.Tree => A): List[A] =
  {
    Export.read_entry(db, session_name, theory_name, "theory/" + export_name) match {
      case Some(entry) => entry.uncompressed_yxml().map(decode(_))
      case None => Nil
    }
  }


  /* types */

  sealed case class Type(entity: Entity, args: List[String], abbrev: Option[Term.Typ])

  def read_types(db: SQL.Database, session_name: String, theory_name: String): List[Type] =
    read_entities(db, session_name, theory_name, "types",
      (tree: XML.Tree) =>
        {
          val (entity, body) = decode_entity(tree)
          val (args, abbrev) =
          {
            import XML.Decode._
            pair(list(string), option(Term_XML.Decode.typ))(body)
          }
          Type(entity, args, abbrev)
        })


  /* consts */

  sealed case class Const(
    entity: Entity, typargs: List[String], typ: Term.Typ, abbrev: Option[Term.Term])

  def read_consts(db: SQL.Database, session_name: String, theory_name: String): List[Const] =
    read_entities(db, session_name, theory_name, "consts",
      (tree: XML.Tree) =>
        {
          val (entity, body) = decode_entity(tree)
          val (args, typ, abbrev) =
          {
            import XML.Decode._
            triple(list(string), Term_XML.Decode.typ, option(Term_XML.Decode.term))(body)
          }
          Const(entity, args, typ, abbrev)
        })
}
