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
    thms: Boolean = true,
    classes: Boolean = true,
    locales: Boolean = true,
    locale_dependencies: Boolean = true,
    classrel: Boolean = true,
    arities: Boolean = true,
    typedefs: Boolean = true,
    cache: Term.Cache = Term.make_cache()): Session =
  {
    val thys =
      using(store.open_database(session_name))(db =>
      {
        db.transaction {
          Export.read_theory_names(db, session_name).map((theory_name: String) =>
            read_theory(Export.Provider.database(db, session_name, theory_name),
              session_name, theory_name, types = types, consts = consts,
              axioms = axioms, thms = thms, classes = classes, locales = locales,
              locale_dependencies = locale_dependencies, classrel = classrel, arities = arities,
              typedefs = typedefs, cache = Some(cache)))
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
  val export_prefix_proofs: String = "proofs/"

  sealed case class Theory(name: String, parents: List[String],
    types: List[Type],
    consts: List[Const],
    axioms: List[Axiom],
    thms: List[Thm],
    classes: List[Class],
    locales: List[Locale],
    locale_dependencies: List[Locale_Dependency],
    classrel: List[Classrel],
    arities: List[Arity],
    typedefs: List[Typedef])
  {
    override def toString: String = name

    lazy val entities: Set[Long] =
      Set.empty[Long] ++
        types.iterator.map(_.entity.serial) ++
        consts.iterator.map(_.entity.serial) ++
        axioms.iterator.map(_.entity.serial) ++
        thms.iterator.map(_.entity.serial) ++
        classes.iterator.map(_.entity.serial) ++
        locales.iterator.map(_.entity.serial) ++
        locale_dependencies.iterator.map(_.entity.serial)

    def cache(cache: Term.Cache): Theory =
      Theory(cache.string(name),
        parents.map(cache.string(_)),
        types.map(_.cache(cache)),
        consts.map(_.cache(cache)),
        axioms.map(_.cache(cache)),
        thms.map(_.cache(cache)),
        classes.map(_.cache(cache)),
        locales.map(_.cache(cache)),
        locale_dependencies.map(_.cache(cache)),
        classrel.map(_.cache(cache)),
        arities.map(_.cache(cache)),
        typedefs.map(_.cache(cache)))
  }

  def empty_theory(name: String): Theory =
    Theory(name, Nil, Nil, Nil, Nil, Nil, Nil, Nil, Nil, Nil, Nil, Nil)

  def read_theory(provider: Export.Provider, session_name: String, theory_name: String,
    types: Boolean = true,
    consts: Boolean = true,
    axioms: Boolean = true,
    thms: Boolean = true,
    classes: Boolean = true,
    locales: Boolean = true,
    locale_dependencies: Boolean = true,
    classrel: Boolean = true,
    arities: Boolean = true,
    typedefs: Boolean = true,
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
        if (thms) read_thms(provider) else Nil,
        if (classes) read_classes(provider) else Nil,
        if (locales) read_locales(provider) else Nil,
        if (locale_dependencies) read_locale_dependencies(provider) else Nil,
        if (classrel) read_classrel(provider) else Nil,
        if (arities) read_arities(provider) else Nil,
        if (typedefs) read_typedefs(provider) else Nil)
    if (cache.isDefined) theory.cache(cache.get) else theory
  }

  def read_pure_theory(store: Sessions.Store, cache: Option[Term.Cache] = None): Theory =
  {
    val session_name = Thy_Header.PURE
    val theory_name = Thy_Header.PURE

    using(store.open_database(session_name))(db =>
    {
      db.transaction {
        read_theory(Export.Provider.database(db, session_name, theory_name),
          session_name, theory_name, cache = cache)
      }
    })
  }


  /* entities */

  object Kind extends Enumeration
  {
    val TYPE = Value("type")
    val CONST = Value("const")
    val AXIOM = Value("axiom")
    val THM = Value("thm")
    val CLASS = Value("class")
    val LOCALE = Value("locale")
    val LOCALE_DEPENDENCY = Value("locale_dependency")
  }

  sealed case class Entity(
    kind: Kind.Value, name: String, xname: String, pos: Position.T, id: Option[Long], serial: Long)
  {
    override def toString: String = kind.toString + " " + quote(name)

    def cache(cache: Term.Cache): Entity =
      Entity(kind, cache.string(name), cache.string(xname), cache.position(pos), id, serial)
  }

  def decode_entity(kind: Kind.Value, tree: XML.Tree): (Entity, XML.Body) =
  {
    def err(): Nothing = throw new XML.XML_Body(List(tree))

    tree match {
      case XML.Elem(Markup(Markup.ENTITY, props), body) =>
        val name = Markup.Name.unapply(props) getOrElse err()
        val xname = Markup.XName.unapply(props) getOrElse err()
        val pos = props.filter({ case (a, _) => Markup.POSITION_PROPERTIES(a) && a != Markup.ID })
        val id = Position.Id.unapply(props)
        val serial = Markup.Serial.unapply(props) getOrElse err()
        (Entity(kind, name, xname, pos, id, serial), body)
      case _ => err()
    }
  }


  /* approximative syntax */

  object Assoc extends Enumeration
  {
    val NO_ASSOC, LEFT_ASSOC, RIGHT_ASSOC = Value
  }

  sealed abstract class Syntax
  case object No_Syntax extends Syntax
  case class Prefix(delim: String) extends Syntax
  case class Infix(assoc: Assoc.Value, delim: String, pri: Int) extends Syntax

  def decode_syntax: XML.Decode.T[Syntax] =
    XML.Decode.variant(List(
      { case (Nil, Nil) => No_Syntax },
      { case (List(delim), Nil) => Prefix(delim) },
      { case (Nil, body) =>
          import XML.Decode._
          val (ass, delim, pri) = triple(int, string, int)(body)
          Infix(Assoc(ass), delim, pri) }))


  /* types */

  sealed case class Type(
    entity: Entity, syntax: Syntax, args: List[String], abbrev: Option[Term.Typ])
  {
    def cache(cache: Term.Cache): Type =
      Type(entity.cache(cache),
        syntax,
        args.map(cache.string(_)),
        abbrev.map(cache.typ(_)))
  }

  def read_types(provider: Export.Provider): List[Type] =
    provider.uncompressed_yxml(export_prefix + "types").map((tree: XML.Tree) =>
      {
        val (entity, body) = decode_entity(Kind.TYPE, tree)
        val (syntax, args, abbrev) =
        {
          import XML.Decode._
          triple(decode_syntax, list(string), option(Term_XML.Decode.typ))(body)
        }
        Type(entity, syntax, args, abbrev)
      })


  /* consts */

  sealed case class Const(
    entity: Entity,
    syntax: Syntax,
    typargs: List[String],
    typ: Term.Typ,
    abbrev: Option[Term.Term],
    propositional: Boolean,
    primrec_types: List[String],
    corecursive: Boolean)
  {
    def cache(cache: Term.Cache): Const =
      Const(entity.cache(cache),
        syntax,
        typargs.map(cache.string(_)),
        cache.typ(typ),
        abbrev.map(cache.term(_)),
        propositional,
        primrec_types.map(cache.string(_)),
        corecursive)
  }

  def read_consts(provider: Export.Provider): List[Const] =
    provider.uncompressed_yxml(export_prefix + "consts").map((tree: XML.Tree) =>
      {
        val (entity, body) = decode_entity(Kind.CONST, tree)
        val (syntax, (args, (typ, (abbrev, (propositional, (primrec_types, corecursive)))))) =
        {
          import XML.Decode._
          pair(decode_syntax,
            pair(list(string),
              pair(Term_XML.Decode.typ,
                pair(option(Term_XML.Decode.term), pair(bool,
                  pair(list(string), bool))))))(body)
        }
        Const(entity, syntax, args, typ, abbrev, propositional, primrec_types, corecursive)
      })


  /* axioms */

  sealed case class Prop(
    typargs: List[(String, Term.Sort)],
    args: List[(String, Term.Typ)],
    term: Term.Term)
  {
    def cache(cache: Term.Cache): Prop =
      Prop(
        typargs.map({ case (name, sort) => (cache.string(name), cache.sort(sort)) }),
        args.map({ case (name, typ) => (cache.string(name), cache.typ(typ)) }),
        cache.term(term))
  }

  def decode_prop(body: XML.Body): Prop =
  {
    val (typargs, args, t) =
    {
      import XML.Decode._
      import Term_XML.Decode._
      triple(list(pair(string, sort)), list(pair(string, typ)), term)(body)
    }
    Prop(typargs, args, t)
  }

  sealed case class Axiom(entity: Entity, prop: Prop)
  {
    def cache(cache: Term.Cache): Axiom =
      Axiom(entity.cache(cache), prop.cache(cache))
  }

  def read_axioms(provider: Export.Provider): List[Axiom] =
    provider.uncompressed_yxml(export_prefix + "axioms").map((tree: XML.Tree) =>
      {
        val (entity, body) = decode_entity(Kind.AXIOM, tree)
        val prop = decode_prop(body)
        Axiom(entity, prop)
      })


  /* theorems */

  sealed case class Thm(entity: Entity, prop: Prop, proof: Option[Term.Proof])
  {
    def cache(cache: Term.Cache): Thm =
      Thm(entity.cache(cache), prop.cache(cache), proof.map(cache.proof _))
  }

  def read_thms(provider: Export.Provider): List[Thm] =
    provider.uncompressed_yxml(export_prefix + "thms").map((tree: XML.Tree) =>
      {
        val (entity, body) = decode_entity(Kind.THM, tree)
        val (prop, prf) =
        {
          import XML.Decode._
          import Term_XML.Decode._
          pair(decode_prop _, option(proof))(body)
        }
        Thm(entity, prop, prf)
      })

  def read_proof(
    provider: Export.Provider,
    theory_name: String,
    serial: Long,
    cache: Option[Term.Cache] = None): (Term.Term, Term.Proof) =
  {
    val body = provider.focus(theory_name).uncompressed_yxml(export_prefix_proofs + serial)
    if (body.isEmpty) error("Bad proof export " + serial)
    val (prop, proof) = XML.Decode.pair(Term_XML.Decode.term, Term_XML.Decode.proof)(body)
    cache match {
      case None => (prop, proof)
      case Some(cache) => (cache.term(prop), cache.proof(proof))
    }
  }


  /* type classes */

  sealed case class Class(
    entity: Entity, params: List[(String, Term.Typ)], axioms: List[Prop])
  {
    def cache(cache: Term.Cache): Class =
      Class(entity.cache(cache),
        params.map({ case (name, typ) => (cache.string(name), cache.typ(typ)) }),
        axioms.map(_.cache(cache)))
  }

  def read_classes(provider: Export.Provider): List[Class] =
    provider.uncompressed_yxml(export_prefix + "classes").map((tree: XML.Tree) =>
      {
        val (entity, body) = decode_entity(Kind.CLASS, tree)
        val (params, axioms) =
        {
          import XML.Decode._
          import Term_XML.Decode._
          pair(list(pair(string, typ)), list(decode_prop))(body)
        }
        Class(entity, params, axioms)
      })


  /* locales */

  sealed case class Locale(
    entity: Entity,
    typargs: List[(String, Term.Sort)],
    args: List[((String, Term.Typ), Syntax)],
    axioms: List[Prop])
  {
    def cache(cache: Term.Cache): Locale =
      Locale(entity.cache(cache),
        typargs.map({ case (name, sort) => (cache.string(name), cache.sort(sort)) }),
        args.map({ case ((name, typ), syntax) => ((cache.string(name), cache.typ(typ)), syntax) }),
        axioms.map(_.cache(cache)))
  }

  def read_locales(provider: Export.Provider): List[Locale] =
    provider.uncompressed_yxml(export_prefix + "locales").map((tree: XML.Tree) =>
      {
        val (entity, body) = decode_entity(Kind.LOCALE, tree)
        val (typargs, args, axioms) =
        {
          import XML.Decode._
          import Term_XML.Decode._
          triple(list(pair(string, sort)), list(pair(pair(string, typ), decode_syntax)),
            list(decode_prop))(body)
        }
        Locale(entity, typargs, args, axioms)
      })


  /* locale dependencies */

  sealed case class Locale_Dependency(
    entity: Entity,
    source: String,
    target: String,
    prefix: List[(String, Boolean)],
    subst_types: List[((String, Term.Sort), Term.Typ)],
    subst_terms: List[((String, Term.Typ), Term.Term)])
  {
    def cache(cache: Term.Cache): Locale_Dependency =
      Locale_Dependency(entity.cache(cache),
        cache.string(source),
        cache.string(target),
        prefix.map({ case (name, mandatory) => (cache.string(name), mandatory) }),
        subst_types.map({ case ((a, s), ty) => ((cache.string(a), cache.sort(s)), cache.typ(ty)) }),
        subst_terms.map({ case ((x, ty), t) => ((cache.string(x), cache.typ(ty)), cache.term(t)) }))

    def is_inclusion: Boolean =
      subst_types.isEmpty && subst_terms.isEmpty
  }

  def read_locale_dependencies(provider: Export.Provider): List[Locale_Dependency] =
    provider.uncompressed_yxml(export_prefix + "locale_dependencies").map((tree: XML.Tree) =>
      {
        val (entity, body) = decode_entity(Kind.LOCALE_DEPENDENCY, tree)
        val (source, (target, (prefix, (subst_types, subst_terms)))) =
        {
          import XML.Decode._
          import Term_XML.Decode._
          pair(string, pair(string, pair(list(pair(string, bool)),
            pair(list(pair(pair(string, sort), typ)), list(pair(pair(string, typ), term))))))(body)
        }
        Locale_Dependency(entity, source, target, prefix, subst_types, subst_terms)
      })


  /* sort algebra */

  sealed case class Classrel(class1: String, class2: String, prop: Prop)
  {
    def cache(cache: Term.Cache): Classrel =
      Classrel(cache.string(class1), cache.string(class2), prop.cache(cache))
  }

  def read_classrel(provider: Export.Provider): List[Classrel] =
  {
    val body = provider.uncompressed_yxml(export_prefix + "classrel")
    val classrel =
    {
      import XML.Decode._
      list(pair(decode_prop, pair(string, string)))(body)
    }
    for ((prop, (c1, c2)) <- classrel) yield Classrel(c1, c2, prop)
  }

  sealed case class Arity(type_name: String, domain: List[Term.Sort], codomain: String, prop: Prop)
  {
    def cache(cache: Term.Cache): Arity =
      Arity(cache.string(type_name), domain.map(cache.sort(_)), cache.string(codomain),
        prop.cache(cache))
  }

  def read_arities(provider: Export.Provider): List[Arity] =
  {
    val body = provider.uncompressed_yxml(export_prefix + "arities")
    val arities =
    {
      import XML.Decode._
      import Term_XML.Decode._
      list(pair(decode_prop, triple(string, list(sort), string)))(body)
    }
    for ((prop, (a, b, c)) <- arities) yield Arity(a, b, c, prop)
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
