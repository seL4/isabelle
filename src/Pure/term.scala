/*  Title:      Pure/term.scala
    Author:     Makarius

Lambda terms with XML data representation.

Note: Isabelle/ML is the primary environment for logical operations.
*/

package isabelle


object Term
{
  /* basic type definitions */

  type Indexname = (String, Int)

  type Sort = List[String]
  val dummyS: Sort = List("")

  sealed abstract class Typ
  case class Type(name: String, args: List[Typ] = Nil) extends Typ
  case class TFree(name: String, sort: Sort = dummyS) extends Typ
  case class TVar(name: Indexname, sort: Sort = dummyS) extends Typ
  val dummyT = Type("dummy")

  sealed abstract class Term
  case class Const(name: String, typ: Typ = dummyT) extends Term
  case class Free(name: String, typ: Typ = dummyT) extends Term
  case class Var(name: Indexname, typ: Typ = dummyT) extends Term
  case class Bound(index: Int) extends Term
  case class Abs(name: String, typ: Typ = dummyT, body: Term) extends Term
  case class App(fun: Term, arg: Term) extends Term
}


object Term_XML
{
  import Term._


  /* XML data representation */

  object Encode
  {
    import XML.Encode._

    val sort: T[Sort] = list(string)

    def typ: T[Typ] =
      variant[Typ](List(
        { case Type(a, b) => (List(a), list(typ)(b)) },
        { case TFree(a, b) => (List(a), sort(b)) },
        { case TVar((a, b), c) => (List(a, int_atom(b)), sort(c)) }))

    def term: T[Term] =
      variant[Term](List(
        { case Const(a, b) => (List(a), typ(b)) },
        { case Free(a, b) => (List(a), typ(b)) },
        { case Var((a, b), c) => (List(a, int_atom(b)), typ(c)) },
        { case Bound(a) => (List(int_atom(a)), Nil) },
        { case Abs(a, b, c) => (List(a), pair(typ, term)(b, c)) },
        { case App(a, b) => (Nil, pair(term, term)(a, b)) }))
  }

  object Decode
  {
    import XML.Decode._

    val sort: T[Sort] = list(string)

    def typ: T[Typ] =
      variant[Typ](List(
        { case (List(a), b) => Type(a, list(typ)(b)) },
        { case (List(a), b) => TFree(a, sort(b)) },
        { case (List(a, b), c) => TVar((a, int_atom(b)), sort(c)) }))

    def term: T[Term] =
      variant[Term](List(
        { case (List(a), b) => Const(a, typ(b)) },
        { case (List(a), b) => Free(a, typ(b)) },
        { case (List(a, b), c) => Var((a, int_atom(b)), typ(c)) },
        { case (List(a), Nil) => Bound(int_atom(a)) },
        { case (List(a), b) => val (c, d) = pair(typ, term)(b); Abs(a, c, d) },
        { case (Nil, a) => val (b, c) = pair(term, term)(a); App(b, c) }))
  }
}
