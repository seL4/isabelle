/* Author: Pascal Stoop, ETH Zurich
   Author: Andreas Lochbihler, Digital Asset */

object Lazy {
  final class Lazy[A] (f: Unit => A) {
    var evaluated = false;
    lazy val x: A = f(())

    def get() : A = {
      evaluated = true;
      return x
    }
  }

  def force[A] (x: Lazy[A]) : A = {
    return x.get()
  }

  def delay[A] (f: Unit => A) : Lazy[A] = {
    return new Lazy[A] (f)
  }

  def termify_lazy[Typerep, Term, A] (
    const: String => Typerep => Term,
    app: Term => Term => Term,
    abs: String => Typerep => Term => Term,
    unitT: Typerep,
    funT: Typerep => Typerep => Typerep,
    lazyT: Typerep => Typerep,
    term_of: A => Term,
    ty: Typerep,
    x: Lazy[A],
    dummy: Term) : Term = {
    x.evaluated match {
      case true => app(const("Code_Lazy.delay")(funT(funT(unitT)(ty))(lazyT(ty))))(abs("_")(unitT)(term_of(x.get())))
      case false => app(const("Code_Lazy.delay")(funT(funT(unitT)(ty))(lazyT(ty))))(const("Pure.dummy_pattern")(funT(unitT)(ty)))
    }
  }
}
