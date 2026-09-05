/*  Title:      Pure/Thy/thy_conditions.scala
    Author:     Makarius

Side-conditions on processing the body of a theory file.
*/

package isabelle


import scala.collection.immutable.SortedMap


object Thy_Conditions {
  val option = "condition"

  def init(session_options: Options): Thy_Conditions =
    new Thy_Conditions(session_options, SortedMap.empty)

  def explode(options: Options): List[String] =
    space_explode(',', options.string(option))


  /* context with mutable state (or cache) */

  final class Context(init_options: Options) {
    private var conditions: Thy_Conditions = Thy_Conditions.init(init_options)

    def value: Thy_Conditions = synchronized { conditions }
    override def toString: String = value.toString

    def init(options: Options): Thy_Conditions =
      synchronized { conditions = Thy_Conditions.init(options); conditions }

    def eval_restrict(specs: Options.Update): Thy_Conditions = synchronized {
      val options = conditions.options(specs)
      val conds = Thy_Conditions.explode(options)
      conditions = conditions.evaluate(conds)
      conditions.restrict(conds.toSet)
    }
  }
}

final class Thy_Conditions private(
  session_options: Options,
  rep: SortedMap[String, Exn.Result[Boolean]]
) {
  def restrict(domain: Set[String]): Thy_Conditions =
    new Thy_Conditions(session_options, rep.filter(p => domain(p._1)))

  def dest[A](f: (String, Boolean) => A): List[A] =
    List.from(for (case (a, Exn.Res(b)) <- rep.iterator) yield f(a, b))
  def errors: List[String] =
    List.from(for (case (_, Exn.Exn(e)) <- rep.iterator) yield Exn.message(e))
  def good: List[String] = List.from(for (case (a, Exn.Res(true)) <- rep.iterator) yield a)
  def bad: List[String] = List.from(for (case (a, Exn.Res(false)) <- rep.iterator) yield a)
  def bad_message: String =
    bad match {
      case Nil => ""
      case xs => xs.map(x => "undefined " + x).mkString("(", ", ", ")")
    }

  def check_errors: Thy_Conditions =
    errors match {
      case Nil => this
      case errs => error(cat_lines(errs))
    }

  def options(specs: Options.Update): Options =
    session_options ++ specs.filter(p => p._1 == Thy_Conditions.option)

  def evaluate(cond: String): Thy_Conditions =
    if (rep.isDefinedAt(cond)) this
    else {
      val result =
        Exn.result(
          Library.try_unprefix("$", cond) match {
            case Some(a) => Isabelle_System.getenv(a).nonEmpty
            case None =>
              try { session_options.proper_value(cond) }
              catch {
                case ERROR(msg) => error(msg + " (use \"$NAME\" for environment variables)")
              }
          }
        )
      new Thy_Conditions(session_options, rep + (cond -> result))
    }

  def evaluate(conds: List[String]): Thy_Conditions = conds.foldLeft(this)(_ evaluate _)

  def eval(options: Options): Thy_Conditions = evaluate(Thy_Conditions.explode(options))
  def eval(specs: Options.Update): Thy_Conditions = eval(options(specs))

  override def toString: String = {
    val a = if_proper(good, "good = " + quote(good.mkString(",")))
    val b = if_proper(bad, "bad = " + quote(bad.mkString(",")))
    "Thy_Conditions(" + a + if_proper(a.nonEmpty && b.nonEmpty, ", ") + b + ")"
  }
}
