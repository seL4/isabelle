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

  def read_session(store: Sessions.Store,
    session_name: String,
    types: Boolean = true,
    consts: Boolean = true,
    axioms: Boolean = true,
    facts: Boolean = true,
    classes: Boolean = true,
    typedefs: Boolean = true,
    classrel: Boolean = true,
    arities: Boolean = true,
    cache: Term.Cache = Term.make_cache()): Session =
  {
    val thys =
      using(store.open_database(session_name))(db =>
      {
        db.transaction {
          Export.read_theory_names(db, session_name).map((theory_name: String) =>
            read_theory(Export.Provider.database(db, session_name, theory_name),
              session_name, theory_name, types = types, consts = consts,
              axioms = axioms, facts = facts, classes = classes, typedefs = typedefs,
              cache = Some(cache)))
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

  val export_prefix: String = "theory/"

  sealed case class Theory(name: String, parents: List[String],
    types: List[Type],
    consts: List[Const],
    axioms: List[Axiom],
    facts: List[Fact],
    classes: List[Class],
    typedefs: List[Typedef],
    classrel: List[Classrel],
    arities: List[Arity])
  {
    override def toString: String = name

    def cache(cache: Term.Cache): Theory =
      Theory(cache.string(name),
        parents.map(cache.string(_)),
        types.map(_.cache(cache)),
        consts.map(_.cache(cache)),
        axioms.map(_.cache(cache)),
        facts.map(_.cache(cache)),
        classes.map(_.cache(cache)),
        typedefs.map(_.cache(cache)),
        classrel.map(_.cache(cache)),
        arities.map(_.cache(cache)))
  }

  def empty_theory(name: String): Theory =
    Theory(name, Nil, Nil, Nil, Nil, Nil, Nil, Nil, Nil, Nil)

  def read_theory(provider: Export.Provider, session_name: String, theory_name: String,
    types: Boolean = true,
    consts: Boolean = true,
    axioms: Boolean = true,
    facts: Boolean = true,
    classes: Boolean = true,
    typedefs: Boolean = true,
    classrel: Boolean = true,
    arities: Boolean = true,
    cache: Option[Term.Cache] = None): Theory =
  {
    val parents =
      provider(export_prefix + "parents") match {
        case Some(entry) => split_lines(entry.uncompressed().text)
        case None =>
          error("Missing theory export in session " + quote(session_name) + ": " +
            quote(theory_name))
      }
    val theory =
      Theory(theory_name, parents,
        if (types) read_types(provider) else Nil,
        if (consts) read_consts(provider) else Nil,
        if (axioms) read_axioms(provider) else Nil,
        if (facts) read_facts(provider) else Nil,
        if (classes) read_classes(provider) else Nil,
        if (typedefs) read_typedefs(provider) else Nil,
        if (classrel) read_classrel(provider) else Nil,
        if (arities) read_arities(provider) else Nil)
    if (cache.isDefined) theory.cache(cache.get) else theory
  }


  /* entities */

  sealed case class Entity(name: String, serial: Long, pos: Position.T)
  {
    override def toString: String = name

    def cache(cache: Term.Cache): Entity =
      Entity(cache.string(name), serial, cache.position(pos))
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
    def cache(cache: Term.Cache): Type =
      Type(entity.cache(cache),
        args.map(cache.string(_)),
        abbrev.map(cache.typ(_)))
  }

  def read_types(provider: Export.Provider): List[Type] =
    provider.uncompressed_yxml(export_prefix + "types").map((tree: XML.Tree) =>
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
  {
    def cache(cache: Term.Cache): Const =
      Const(entity.cache(cache),
        typargs.map(cache.string(_)),
        cache.typ(typ),
        abbrev.map(cache.term(_)))
  }

  def read_consts(provider: Export.Provider): List[Const] =
    provider.uncompressed_yxml(export_prefix + "consts").map((tree: XML.Tree) =>
      {
        val (entity, body) = decode_entity(tree)
        val (args, typ, abbrev) =
        {
          import XML.Decode._
          triple(list(string), Term_XML.Decode.typ, option(Term_XML.Decode.term))(body)
        }
        Const(entity, args, typ, abbrev)
      })


  /* axioms and facts */

  def decode_props(body: XML.Body):
    (List[(String, Term.Sort)], List[(String, Term.Typ)], List[Term.Term]) =
  {
    import XML.Decode._
    import Term_XML.Decode._
    triple(list(pair(string, sort)), list(pair(string, typ)), list(term))(body)
  }

  sealed case class Axiom(
    entity: Entity,
    typargs: List[(String, Term.Sort)],
    args: List[(String, Term.Typ)],
    prop: Term.Term)
  {
    def cache(cache: Term.Cache): Axiom =
      Axiom(entity.cache(cache),
        typargs.map({ case (name, sort) => (cache.string(name), cache.sort(sort)) }),
        args.map({ case (name, typ) => (cache.string(name), cache.typ(typ)) }),
        cache.term(prop))
  }

  def read_axioms(provider: Export.Provider): List[Axiom] =
    provider.uncompressed_yxml(export_prefix + "axioms").map((tree: XML.Tree) =>
      {
        val (entity, body) = decode_entity(tree)
        val (typargs, args, List(prop)) = decode_props(body)
        Axiom(entity, typargs, args, prop)
      })

  sealed case class Fact(
    entity: Entity,
    typargs: List[(String, Term.Sort)],
    args: List[(String, Term.Typ)],
    props: List[Term.Term])
  {
    def cache(cache: Term.Cache): Fact =
      Fact(entity.cache(cache),
        typargs.map({ case (name, sort) => (cache.string(name), cache.sort(sort)) }),
        args.map({ case (name, typ) => (cache.string(name), cache.typ(typ)) }),
        props.map(cache.term(_)))
  }

  def read_facts(provider: Export.Provider): List[Fact] =
    provider.uncompressed_yxml(export_prefix + "facts").map((tree: XML.Tree) =>
      {
        val (entity, body) = decode_entity(tree)
        val (typargs, args, props) = decode_props(body)
        Fact(entity, typargs, args, props)
      })


  /* type classes */

  sealed case class Class(
    entity: Entity, params: List[(String, Term.Typ)], axioms: List[Term.Term])
  {
    def cache(cache: Term.Cache): Class =
      Class(entity.cache(cache),
        params.map({ case (name, typ) => (cache.string(name), cache.typ(typ)) }),
        axioms.map(cache.term(_)))
  }

  def read_classes(provider: Export.Provider): List[Class] =
    provider.uncompressed_yxml(export_prefix + "classes").map((tree: XML.Tree) =>
      {
        val (entity, body) = decode_entity(tree)
        val (params, axioms) =
        {
          import XML.Decode._
          import Term_XML.Decode._
          pair(list(pair(string, typ)), list(term))(body)
        }
        Class(entity, params, axioms)
      })


  /* sort algebra */

  sealed case class Classrel(class_name: String, super_names: List[String])
  {
    def cache(cache: Term.Cache): Classrel =
      Classrel(cache.string(class_name), super_names.map(cache.string(_)))
  }

  def read_classrel(provider: Export.Provider): List[Classrel] =
  {
    val body = provider.uncompressed_yxml(export_prefix + "classrel")
    val classrel =
    {
      import XML.Decode._
      list(pair(string, list(string)))(body)
    }
    for ((c, cs) <- classrel) yield Classrel(c, cs)
  }

  sealed case class Arity(type_name: String, domain: List[Term.Sort], codomain: String)
  {
    def cache(cache: Term.Cache): Arity =
      Arity(cache.string(type_name), domain.map(cache.sort(_)), cache.string(codomain))
  }

  def read_arities(provider: Export.Provider): List[Arity] =
  {
    val body = provider.uncompressed_yxml(export_prefix + "arities")
    val arities =
    {
      import XML.Decode._
      import Term_XML.Decode._
      list(triple(string, list(sort), string))(body)
    }
    for ((a, b, c) <- arities) yield Arity(a, b, c)
  }


  /* HOL typedefs */

  sealed case class Typedef(name: String,
    rep_type: Term.Typ, abs_type: Term.Typ, rep_name: String, abs_name: String, axiom_name: String)
  {
    def cache(cache: Term.Cache): Typedef =
      Typedef(cache.string(name),
        cache.typ(rep_type),
        cache.typ(abs_type),
        cache.string(rep_name),
        cache.string(abs_name),
        cache.string(axiom_name))
  }

  def read_typedefs(provider: Export.Provider): List[Typedef] =
  {
    val body = provider.uncompressed_yxml(export_prefix + "typedefs")
    val typedefs =
    {
      import XML.Decode._
      import Term_XML.Decode._
      list(pair(string, pair(typ, pair(typ, pair(string, pair(string, string))))))(body)
    }
    for { (name, (rep_type, (abs_type, (rep_name, (abs_name, axiom_name))))) <- typedefs }
    yield Typedef(name, rep_type, abs_type, rep_name, abs_name, axiom_name)
  }
}
