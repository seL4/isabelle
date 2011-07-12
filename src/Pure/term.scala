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

    val indexname: T[Indexname] = pair(string, int)

    val sort: T[Sort] = list(string)

    def typ: T[Typ] =
      variant[Typ](List(
        { case Type(a, b) => pair(string, list(typ))((a, b)) },
        { case TFree(a, b) => pair(string, sort)((a, b)) },
        { case TVar(a, b) => pair(indexname, sort)((a, b)) }))

    def term: T[Term] =
      variant[Term](List(
        { case Const(a, b) => pair(string, typ)((a, b)) },
        { case Free(a, b) => pair(string, typ)((a, b)) },
        { case Var(a, b) => pair(indexname, typ)((a, b)) },
        { case Bound(a) => int(a) },
        { case Abs(a, b, c) => triple(string, typ, term)((a, b, c)) },
        { case App(a, b) => pair(term, term)((a, b)) }))
  }

  object Decode
  {
    import XML.Decode._

    val indexname: T[Indexname] = pair(string, int)

    val sort: T[Sort] = list(string)

    def typ: T[Typ] =
      variant[Typ](List(
        (x => { val (a, b) = pair(string, list(typ))(x); Type(a, b) }),
        (x => { val (a, b) = pair(string, sort)(x); TFree(a, b) }),
        (x => { val (a, b) = pair(indexname, sort)(x); TVar(a, b) })))

    def term: T[Term] =
      variant[Term](List(
        (x => { val (a, b) = pair(string, typ)(x); Const(a, b) }),
        (x => { val (a, b) = pair(string, typ)(x); Free(a, b) }),
        (x => { val (a, b) = pair(indexname, typ)(x); Var(a, b) }),
        (x => Bound(int(x))),
        (x => { val (a, b, c) = triple(string, typ, term)(x); Abs(a, b, c) }),
        (x => { val (a, b) = pair(term, term)(x); App(a, b) })))
  }
}
