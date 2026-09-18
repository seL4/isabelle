/*  Title:      Pure/Thy/thy_conditions.scala
    Author:     Makarius

Side-conditions on processing the body of a theory file.
*/

package isabelle


import scala.collection.immutable.SortedMap


object Thy_Conditions {
  object Condition extends Shasum.Special_Entry("condition")

  def init(background: Sessions.Background, options: Options): Thy_Conditions =
    new Thy_Conditions(background, options, SortedMap.empty)

  def explode(options: Options): List[String] =
    space_explode(',', options.string(Condition.name))


  /* context with mutable state (or cache) */

  object Context {
    def apply(background: Sessions.Background, options: Options): Context = {
      val context = new Context
      context.init(background, options)
      context
    }
  }

  final class Context private {
    private var conditions: Thy_Conditions =
      Thy_Conditions.init(Sessions.background0(""), Options.defaults)

    def value: Thy_Conditions = synchronized { conditions }
    override def toString: String = value.toString

    def init(init_background: Sessions.Background, init_options: Options): Unit =
      synchronized { conditions = Thy_Conditions.init(init_background, init_options) }

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
  val background: Sessions.Background,
  val options: Options,
  rep: SortedMap[String, Exn.Result[String]]
) {
  def restrict(domain: Set[String]): Thy_Conditions =
    new Thy_Conditions(background, options, rep.filter(p => domain(p._1)))

  def errors: List[String] =
    List.from(for (case (_, Exn.Exn(e)) <- rep.iterator) yield Exn.message(e))

  def check_errors: Thy_Conditions =
    errors match {
      case Nil => this
      case errs => error(cat_lines(errs))
    }

  def shasum: Shasum = {
    check_errors
    Shasum.flat(List.from(
      for (case (a, Exn.Res(b)) <- rep.iterator)
        yield Shasum.make(SHA1.digest(b), Thy_Conditions.Condition.make(a))))
  }

  def failed: List[String] = List.from(for (case (a, Exn.Exn(_)) <- rep.iterator) yield a)
  def good: List[String] = List.from(for (case (a, Exn.Res("")) <- rep.iterator) yield a)
  def bad: List[String] = List.from(for (case (a, Exn.Res(b)) <- rep.iterator if b.nonEmpty) yield a)
  def bad_message: String = {
    val bads =
      List.from(
        for (case (a, Exn.Res(b)) <- rep.iterator if b.nonEmpty)
          yield "condition " + quote(a) + " is " + b)
    if (bads.isEmpty) "" else bads.mkString("(", ", ", ")")
  }

  def update_options(specs: Options.Update): Options =
    options ++ specs.filter(p => p._1 == Thy_Conditions.Condition.name)

  def evaluate(cond: String): Thy_Conditions =
    if (rep.isDefinedAt(cond)) this
    else {
      def eval_env: Option[String] =
        Library.try_unprefix("$", cond).map(a =>
          if (Isabelle_System.getenv(a).nonEmpty) "" else "empty/unset")

      def eval_pred: Option[String] =
        Library.try_unsuffix("()", cond).map(a =>
          if (Thy_Conditions.the_predicate(a)(this)) "" else "false")

      def eval_bool: Option[String] =
        Value.Boolean.unapply(cond).map(b => if (b) "" else "false")

      def eval_option: String =
        options.get(cond).map(_.typ) match {
          case Some(Options.Bool) => if (options.bool(cond)) "" else "false"
          case Some(Options.Int) =>
            options.int(cond) match {
              case x if x > 0 => ""
              case x if x < 0 => "< 0"
              case 0 => "0"
            }
          case Some(Options.Real) =>
            options.real(cond) compare 0.0 match {
              case x if x > 0.0 && java.lang.Double.isFinite(x) => ""
              case x if x < 0.0 && java.lang.Double.isFinite(x) => "< 0"
              case 0.0 => "0"
              case x => "ill-defined"
            }
          case Some(Options.String) => if (options.string(cond).nonEmpty) "" else "empty"
          case _ =>
            error("Condition " + quote(cond) + " cannot be evaluated as system option" +
              "\n(environment variables need to be given as \"$NAME\")")
        }

      val result = Exn.result(eval_env orElse eval_pred orElse eval_bool getOrElse eval_option)
      new Thy_Conditions(background, options, rep + (cond -> result))
    }

  def evaluate(conds: List[String]): Thy_Conditions = conds.foldLeft(this)(_ evaluate _)

  def eval(opts: Options): Thy_Conditions = evaluate(Thy_Conditions.explode(opts))
  def eval(specs: Options.Update): Thy_Conditions = eval(update_options(specs))

  override def toString: String = {
    val a = if_proper(failed, "failed = " + quote(failed.mkString(",")))
    val b = if_proper(good, "good = " + quote(good.mkString(",")))
    val c = if_proper(bad, "bad = " + quote(bad.mkString(",")))
    List(a, b, c).filterNot(_.isEmpty).mkString("Thy_Conditions(", ", ", ")")
  }
}
