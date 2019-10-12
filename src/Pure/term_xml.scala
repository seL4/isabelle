/*  Title:      Pure/term_xml.scala
    Author:     Makarius

XML data representation of lambda terms.
*/

package isabelle


object Term_XML
{
  import Term._

  object Encode
  {
    import XML.Encode._

    val indexname: P[Indexname] =
      { case Indexname(a, 0) => List(a)
        case Indexname(a, b) => List(a, int_atom(b)) }

    val sort: T[Sort] = list(string)

    def typ: T[Typ] =
      variant[Typ](List(
        { case Type(a, b) => (List(a), list(typ)(b)) },
        { case TFree(a, b) => (List(a), sort(b)) },
        { case TVar(a, b) => (indexname(a), sort(b)) }))

    val typ_body: T[Typ] = (t: Typ) => if (t == dummyT) Nil else typ(t)

    def term: T[Term] =
      variant[Term](List(
        { case Const(a, b) => (List(a), list(typ)(b)) },
        { case Free(a, b) => (List(a), typ_body(b)) },
        { case Var(a, b) => (indexname(a), typ_body(b)) },
        { case Bound(a) => (List(int_atom(a)), Nil) },
        { case Abs(a, b, c) => (List(a), pair(typ, term)(b, c)) },
        { case App(a, b) => (Nil, pair(term, term)(a, b)) }))
  }

  object Decode
  {
    import XML.Decode._

    val indexname: P[Indexname] =
      { case List(a) => Indexname(a, 0)
        case List(a, b) => Indexname(a, int_atom(b)) }

    val sort: T[Sort] = list(string)

    def typ: T[Typ] =
      variant[Typ](List(
        { case (List(a), b) => Type(a, list(typ)(b)) },
        { case (List(a), b) => TFree(a, sort(b)) },
        { case (a, b) => TVar(indexname(a), sort(b)) }))

    val typ_body: T[Typ] = { case Nil => dummyT case body => typ(body) }

    def term: T[Term] =
      variant[Term](List(
        { case (List(a), b) => Const(a, list(typ)(b)) },
        { case (List(a), b) => Free(a, typ_body(b)) },
        { case (a, b) => Var(indexname(a), typ_body(b)) },
        { case (List(a), Nil) => Bound(int_atom(a)) },
        { case (List(a), b) => val (c, d) = pair(typ, term)(b); Abs(a, c, d) },
        { case (Nil, a) => val (b, c) = pair(term, term)(a); App(b, c) }))

    def proof: T[Proof] =
      variant[Proof](List(
        { case (Nil, Nil) => MinProof },
        { case (List(a), Nil) => PBound(int_atom(a)) },
        { case (List(a), b) => val (c, d) = pair(typ, proof)(b); Abst(a, c, d) },
        { case (List(a), b) => val (c, d) = pair(term, proof)(b); AbsP(a, c, d) },
        { case (Nil, a) => val (b, c) = pair(proof, term)(a); Appt(b, c) },
        { case (Nil, a) => val (b, c) = pair(proof, proof)(a); AppP(b, c) },
        { case (Nil, a) => Hyp(term(a)) },
        { case (List(a), b) => PAxm(a, list(typ)(b)) },
        { case (List(a), b) => OfClass(typ(b), a) },
        { case (List(a), b) => val (c, d) = pair(term, list(typ))(b); Oracle(a, c, d) },
        { case (List(a, b, c), d) => PThm(long_atom(a), b, c, list(typ)(d)) }))
  }
}
