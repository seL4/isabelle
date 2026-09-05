/*  Title:      Pure/Thy/thy_conditions.scala
    Author:     Makarius

Side-conditions on processing the body of a theory file.
*/

package isabelle


import scala.collection.immutable.SortedMap


object Thy_Conditions {
  val option = "condition"

  def init(options: Options): Thy_Conditions =
    new Thy_Conditions(options, SortedMap.empty)

  def explode(options: Options): List[String] =
    space_explode(',', options.string(option))


  /* context with mutable state (or cache) */

  object Context {
    def apply(options: Options): Context = {
      val context = new Context
      init(options)
      context
    }
  }

  final class Context private {
    private var conditions: Thy_Conditions = Thy_Conditions.init(Options.defaults)

    override def toString: String = synchronized { conditions.toString }

    def options: Options = synchronized { conditions.options }

    def init(init_options: Options): Unit =
      synchronized { conditions = Thy_Conditions.init(init_options) }

    def eval_restrict(specs: Options.Update): Thy_Conditions = synchronized {
      val eval_options = conditions.update_options(specs)
      val conds = Thy_Conditions.explode(eval_options)
      conditions = conditions.evaluate(conds)
      conditions.restrict(conds.toSet)
    }
  }


  /* predicates */

  abstract class Predicate(val name: String) {
    override def toString: String = name
    def apply(conditions: Thy_Conditions): Boolean
  }

  class Predicates(val predicates: Predicate*) extends Isabelle_System.Service

  lazy val predicates: Map[String, Predicate] = {
    Isabelle_System.make_services(classOf[Predicates]).flatMap(_.predicates.iterator)
      .foldLeft(Map.empty[String, Predicate])(
        { case (map, pred) =>
            if (map.isDefinedAt(pred.name)) {
              error("Duplicate theory condition predicate: " + quote(pred.name))
            }
            else map + (pred.name -> pred)
        })
  }

  def the_predicate(name: String): Predicate =
    predicates.getOrElse(name, error("Bad theory condition predicate: " + quote(name)))
}

final class Thy_Conditions private(
  val options: Options,
  rep: SortedMap[String, Exn.Result[Boolean]]
) {
  def restrict(domain: Set[String]): Thy_Conditions =
    new Thy_Conditions(options, rep.filter(p => domain(p._1)))

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

  def update_options(specs: Options.Update): Options =
    options ++ specs.filter(p => p._1 == Thy_Conditions.option)

  def evaluate(cond: String): Thy_Conditions =
    if (rep.isDefinedAt(cond)) this
    else {
      val result =
        Exn.result(
          Library.try_unprefix("$", cond) match {
            case Some(a) => Isabelle_System.getenv(a).nonEmpty
            case None =>
              Library.try_unsuffix("()", cond) match {
                case Some(a) => Thy_Conditions.the_predicate(a)(this)
                case None =>
                  try { options.proper_value(cond) }
                  catch {
                    case ERROR(msg) => error(msg + " (use \"$NAME\" for environment variables)")
                  }
              }
          }
        )
      new Thy_Conditions(options, rep + (cond -> result))
    }

  def evaluate(conds: List[String]): Thy_Conditions = conds.foldLeft(this)(_ evaluate _)

  def eval(opts: Options): Thy_Conditions = evaluate(Thy_Conditions.explode(opts))
  def eval(specs: Options.Update): Thy_Conditions = eval(update_options(specs))

  override def toString: String = {
    val a = if_proper(good, "good = " + quote(good.mkString(",")))
    val b = if_proper(bad, "bad = " + quote(bad.mkString(",")))
    "Thy_Conditions(" + a + if_proper(a.nonEmpty && b.nonEmpty, ", ") + b + ")"
  }
}
