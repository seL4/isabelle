/*  Title:      Pure/Thy/export_theory.scala
    Author:     Makarius

Export foundational theory content.
*/

package isabelle


import scala.collection.immutable.SortedMap


object Export_Theory
{
  /** session content **/

  sealed case class Session(name: String, theory_graph: Graph[String, Option[Theory]])
  {
    override def toString: String = name

    def theory(theory_name: String): Option[Theory] =
      if (theory_graph.defined(theory_name)) theory_graph.get_node(theory_name)
      else None

    def theories: List[Theory] =
      theory_graph.topological_order.flatMap(theory)
  }

  def read_session(
    store: Sessions.Store,
    sessions_structure: Sessions.Structure,
    session_name: String,
    progress: Progress = new Progress,
    cache: Term.Cache = Term.make_cache()): Session =
  {
    val thys =
      sessions_structure.build_requirements(List(session_name)).flatMap(session =>
        using(store.open_database(session))(db =>
        {
          db.transaction {
            for (theory <- Export.read_theory_names(db, session))
            yield {
              progress.echo("Reading theory " + theory)
              read_theory(Export.Provider.database(db, session, theory),
                session, theory, cache = Some(cache))
            }
          }
        }))

    val graph0 =
      (Graph.string[Option[Theory]] /: thys) {
        case (g, thy) => g.default_node(thy.name, Some(thy)) }
    val graph1 =
      (graph0 /: thys) { case (g0, thy) =>
        (g0 /: thy.parents) { case (g1, parent) =>
          g1.default_node(parent, None).add_edge_acyclic(parent, thy.name) } }

    Session(session_name, graph1)
  }



  /** theory content **/

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
    constdefs: List[Constdef],
    typedefs: List[Typedef],
    datatypes: List[Datatype],
    spec_rules: List[Spec_Rule])
  {
    override def toString: String = name

    def entity_iterator: Iterator[Entity] =
      types.iterator.map(_.entity) ++
      consts.iterator.map(_.entity) ++
      axioms.iterator.map(_.entity) ++
      thms.iterator.map(_.entity) ++
      classes.iterator.map(_.entity) ++
      locales.iterator.map(_.entity) ++
      locale_dependencies.iterator.map(_.entity)

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
        constdefs.map(_.cache(cache)),
        typedefs.map(_.cache(cache)),
        datatypes.map(_.cache(cache)),
        spec_rules.map(_.cache(cache)))
  }

  def read_theory(provider: Export.Provider, session_name: String, theory_name: String,
    cache: Option[Term.Cache] = None): Theory =
  {
    val parents =
      if (theory_name == Thy_Header.PURE) Nil
      else {
        provider(Export.THEORY_PREFIX + "parents") match {
          case Some(entry) => split_lines(entry.uncompressed().text)
          case None =>
            error("Missing theory export in session " + quote(session_name) + ": " +
              quote(theory_name))
        }
      }
    val theory =
      Theory(theory_name, parents,
        read_types(provider),
        read_consts(provider),
        read_axioms(provider),
        read_thms(provider),
        read_classes(provider),
        read_locales(provider),
        read_locale_dependencies(provider),
        read_classrel(provider),
        read_arities(provider),
        read_constdefs(provider),
        read_typedefs(provider),
        read_datatypes(provider),
        read_spec_rules(provider))
    if (cache.isDefined) theory.cache(cache.get) else theory
  }

  def read_pure[A](store: Sessions.Store, read: (Export.Provider, String, String) => A): A =
  {
    val session_name = Thy_Header.PURE
    val theory_name = Thy_Header.PURE

    using(store.open_database(session_name))(db =>
    {
      db.transaction {
        read(Export.Provider.database(db, session_name, theory_name), session_name, theory_name)
      }
    })
  }

  def read_pure_theory(store: Sessions.Store, cache: Option[Term.Cache] = None): Theory =
    read_pure(store, read_theory(_, _, _, cache = cache))

  def read_pure_proof(
      store: Sessions.Store, id: Thm_Id, cache: Option[Term.Cache] = None): Option[Proof] =
    read_pure(store, (provider, _, _) => read_proof(provider, id, cache = cache))


  /* entities */

  object Kind extends Enumeration
  {
    val TYPE = Value("type")
    val CONST = Value("const")
    val AXIOM = Value("axiom")
    val THM = Value("thm")
    val PROOF = Value("proof")
    val CLASS = Value("class")
    val LOCALE = Value("locale")
    val LOCALE_DEPENDENCY = Value("locale_dependency")
    val DOCUMENT_HEADING = Value("document_heading")
    val DOCUMENT_TEXT = Value("document_text")
    val PROOF_TEXT = Value("proof_text")
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
    provider.uncompressed_yxml(Export.THEORY_PREFIX + "types").map((tree: XML.Tree) =>
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
    propositional: Boolean)
  {
    def cache(cache: Term.Cache): Const =
      Const(entity.cache(cache),
        syntax,
        typargs.map(cache.string(_)),
        cache.typ(typ),
        abbrev.map(cache.term(_)),
        propositional)
  }

  def read_consts(provider: Export.Provider): List[Const] =
    provider.uncompressed_yxml(Export.THEORY_PREFIX + "consts").map((tree: XML.Tree) =>
      {
        val (entity, body) = decode_entity(Kind.CONST, tree)
        val (syntax, (typargs, (typ, (abbrev, propositional)))) =
        {
          import XML.Decode._
          pair(decode_syntax,
            pair(list(string),
              pair(Term_XML.Decode.typ,
                pair(option(Term_XML.Decode.term), bool))))(body)
        }
        Const(entity, syntax, typargs, typ, abbrev, propositional)
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
    provider.uncompressed_yxml(Export.THEORY_PREFIX + "axioms").map((tree: XML.Tree) =>
      {
        val (entity, body) = decode_entity(Kind.AXIOM, tree)
        val prop = decode_prop(body)
        Axiom(entity, prop)
      })


  /* theorems */

  sealed case class Thm_Id(serial: Long, theory_name: String)
  {
    def pure: Boolean = theory_name == Thy_Header.PURE
  }

  sealed case class Thm(
    entity: Entity,
    prop: Prop,
    deps: List[String],
    proof: Term.Proof)
  {
    def cache(cache: Term.Cache): Thm =
      Thm(
        entity.cache(cache),
        prop.cache(cache),
        deps.map(cache.string _),
        cache.proof(proof))
  }

  def read_thms(provider: Export.Provider): List[Thm] =
    provider.uncompressed_yxml(Export.THEORY_PREFIX + "thms").map((tree: XML.Tree) =>
      {
        val (entity, body) = decode_entity(Kind.THM, tree)
        val (prop, deps, prf) =
        {
          import XML.Decode._
          import Term_XML.Decode._
          triple(decode_prop, list(string), proof)(body)
        }
        Thm(entity, prop, deps, prf)
      })

  sealed case class Proof(
    typargs: List[(String, Term.Sort)],
    args: List[(String, Term.Typ)],
    term: Term.Term,
    proof: Term.Proof)
  {
    def prop: Prop = Prop(typargs, args, term)

    def cache(cache: Term.Cache): Proof =
      Proof(
        typargs.map({ case (name, sort) => (cache.string(name), cache.sort(sort)) }),
        args.map({ case (name, typ) => (cache.string(name), cache.typ(typ)) }),
        cache.term(term),
        cache.proof(proof))
  }

  def read_proof(
    provider: Export.Provider, id: Thm_Id, cache: Option[Term.Cache] = None): Option[Proof] =
  {
    for { entry <- provider.focus(id.theory_name)(Export.PROOFS_PREFIX + id.serial) }
    yield {
      val body = entry.uncompressed_yxml()
      val (typargs, (args, (prop_body, proof_body))) =
      {
        import XML.Decode._
        import Term_XML.Decode._
        pair(list(pair(string, sort)), pair(list(pair(string, typ)), pair(x => x, x => x)))(body)
      }
      val env = args.toMap
      val prop = Term_XML.Decode.term_env(env)(prop_body)
      val proof = Term_XML.Decode.proof_env(env)(proof_body)

      val result = Proof(typargs, args, prop, proof)
      cache.map(result.cache(_)) getOrElse result
    }
  }

  def read_proof_boxes(
    store: Sessions.Store,
    provider: Export.Provider,
    proof: Term.Proof,
    suppress: Thm_Id => Boolean = _ => false,
    cache: Option[Term.Cache] = None): List[(Thm_Id, Proof)] =
  {
    var seen = Set.empty[Long]
    var result = SortedMap.empty[Long, (Thm_Id, Proof)]

    def boxes(context: Option[(Long, Term.Proof)], prf: Term.Proof)
    {
      prf match {
        case Term.Abst(_, _, p) => boxes(context, p)
        case Term.AbsP(_, _, p) => boxes(context, p)
        case Term.Appt(p, _) => boxes(context, p)
        case Term.AppP(p, q) => boxes(context, p); boxes(context, q)
        case thm: Term.PThm if !seen(thm.serial) =>
          seen += thm.serial
          val id = Thm_Id(thm.serial, thm.theory_name)
          if (!suppress(id)) {
            val read =
              if (id.pure) Export_Theory.read_pure_proof(store, id, cache = cache)
              else Export_Theory.read_proof(provider, id, cache = cache)
            read match {
              case Some(p) =>
                result += (thm.serial -> (id -> p))
                boxes(Some((thm.serial, p.proof)), p.proof)
              case None =>
                error("Missing proof " + thm.serial + " (theory " + quote (thm.theory_name) + ")" +
                  (context match {
                    case None => ""
                    case Some((i, p)) => " in proof " + i + ":\n" + p
                  }))
            }
          }
        case _ =>
      }
    }

    boxes(None, proof)
    result.iterator.map(_._2).toList
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
    provider.uncompressed_yxml(Export.THEORY_PREFIX + "classes").map((tree: XML.Tree) =>
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
    provider.uncompressed_yxml(Export.THEORY_PREFIX + "locales").map((tree: XML.Tree) =>
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
    provider.uncompressed_yxml(Export.THEORY_PREFIX + "locale_dependencies").map((tree: XML.Tree) =>
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
    val body = provider.uncompressed_yxml(Export.THEORY_PREFIX + "classrel")
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
    val body = provider.uncompressed_yxml(Export.THEORY_PREFIX + "arities")
    val arities =
    {
      import XML.Decode._
      import Term_XML.Decode._
      list(pair(decode_prop, triple(string, list(sort), string)))(body)
    }
    for ((prop, (a, b, c)) <- arities) yield Arity(a, b, c, prop)
  }


  /* Pure constdefs */

  sealed case class Constdef(name: String, axiom_name: String)
  {
    def cache(cache: Term.Cache): Constdef =
      Constdef(cache.string(name), cache.string(axiom_name))
  }

  def read_constdefs(provider: Export.Provider): List[Constdef] =
  {
    val body = provider.uncompressed_yxml(Export.THEORY_PREFIX + "constdefs")
    val constdefs =
    {
      import XML.Decode._
      list(pair(string, string))(body)
    }
    for ((name, axiom_name) <- constdefs) yield Constdef(name, axiom_name)
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
    val body = provider.uncompressed_yxml(Export.THEORY_PREFIX + "typedefs")
    val typedefs =
    {
      import XML.Decode._
      import Term_XML.Decode._
      list(pair(string, pair(typ, pair(typ, pair(string, pair(string, string))))))(body)
    }
    for { (name, (rep_type, (abs_type, (rep_name, (abs_name, axiom_name))))) <- typedefs }
    yield Typedef(name, rep_type, abs_type, rep_name, abs_name, axiom_name)
  }


  /* HOL datatypes */

  sealed case class Datatype(
    pos: Position.T,
    name: String,
    co: Boolean,
    typargs: List[(String, Term.Sort)],
    typ: Term.Typ,
    constructors: List[(Term.Term, Term.Typ)])
  {
    def id: Option[Long] = Position.Id.unapply(pos)

    def cache(cache: Term.Cache): Datatype =
      Datatype(
        cache.position(pos),
        cache.string(name),
        co,
        typargs.map({ case (name, sort) => (cache.string(name), cache.sort(sort)) }),
        cache.typ(typ),
        constructors.map({ case (term, typ) => (cache.term(term), cache.typ(typ)) }))
  }

  def read_datatypes(provider: Export.Provider): List[Datatype] =
  {
    val body = provider.uncompressed_yxml(Export.THEORY_PREFIX + "datatypes")
    val datatypes =
    {
      import XML.Decode._
      import Term_XML.Decode._
      list(pair(properties, pair(string, pair(bool, pair(list(pair(string, sort)),
            pair(typ, list(pair(term, typ))))))))(body)
    }
    for ((pos, (name, (co, (typargs, (typ, constructors))))) <- datatypes)
      yield Datatype(pos, name, co, typargs, typ, constructors)
  }


  /* Pure spec rules */

  sealed abstract class Recursion
  {
    def cache(cache: Term.Cache): Recursion =
      this match {
        case Primrec(types) => Primrec(types.map(cache.string))
        case Primcorec(types) => Primcorec(types.map(cache.string))
        case _ => this
      }
  }
  case class Primrec(types: List[String]) extends Recursion
  case object Recdef extends Recursion
  case class Primcorec(types: List[String]) extends Recursion
  case object Corec extends Recursion
  case object Unknown_Recursion extends Recursion

  val decode_recursion: XML.Decode.T[Recursion] =
  {
    import XML.Decode._
    variant(List(
      { case (Nil, a) => Primrec(list(string)(a)) },
      { case (Nil, Nil) => Recdef },
      { case (Nil, a) => Primcorec(list(string)(a)) },
      { case (Nil, Nil) => Corec },
      { case (Nil, Nil) => Unknown_Recursion }))
  }


  sealed abstract class Rough_Classification
  {
    def is_equational: Boolean = this.isInstanceOf[Equational]
    def is_inductive: Boolean = this == Inductive
    def is_co_inductive: Boolean = this == Co_Inductive
    def is_relational: Boolean = is_inductive || is_co_inductive
    def is_unknown: Boolean = this == Unknown

    def cache(cache: Term.Cache): Rough_Classification =
      this match {
        case Equational(recursion) => Equational(recursion.cache(cache))
        case _ => this
      }
  }
  case class Equational(recursion: Recursion) extends Rough_Classification
  case object Inductive extends Rough_Classification
  case object Co_Inductive extends Rough_Classification
  case object Unknown extends Rough_Classification

  val decode_rough_classification: XML.Decode.T[Rough_Classification] =
  {
    import XML.Decode._
    variant(List(
      { case (Nil, a) => Equational(decode_recursion(a)) },
      { case (Nil, Nil) => Inductive },
      { case (Nil, Nil) => Co_Inductive },
      { case (Nil, Nil) => Unknown }))
  }


  sealed case class Spec_Rule(
    pos: Position.T,
    name: String,
    rough_classification: Rough_Classification,
    typargs: List[(String, Term.Sort)],
    args: List[(String, Term.Typ)],
    terms: List[(Term.Term, Term.Typ)],
    rules: List[Term.Term])
  {
    def id: Option[Long] = Position.Id.unapply(pos)

    def cache(cache: Term.Cache): Spec_Rule =
      Spec_Rule(
        cache.position(pos),
        cache.string(name),
        rough_classification.cache(cache),
        typargs.map({ case (name, sort) => (cache.string(name), cache.sort(sort)) }),
        args.map({ case (name, typ) => (cache.string(name), cache.typ(typ)) }),
        terms.map({ case (term, typ) => (cache.term(term), cache.typ(typ)) }),
        rules.map(cache.term(_)))
  }

  def read_spec_rules(provider: Export.Provider): List[Spec_Rule] =
  {
    val body = provider.uncompressed_yxml(Export.THEORY_PREFIX + "spec_rules")
    val spec_rules =
    {
      import XML.Decode._
      import Term_XML.Decode._
      list(
        pair(properties, pair(string, pair(decode_rough_classification,
          pair(list(pair(string, sort)), pair(list(pair(string, typ)),
            pair(list(pair(term, typ)), list(term))))))))(body)
    }
    for ((pos, (name, (rough_classification, (typargs, (args, (terms, rules)))))) <- spec_rules)
      yield Spec_Rule(pos, name, rough_classification, typargs, args, terms, rules)
  }
}
