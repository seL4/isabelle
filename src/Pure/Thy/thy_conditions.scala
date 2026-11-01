/*  Title:      Pure/Thy/thy_conditions.scala
    Author:     Makarius

Side-conditions on processing theory body commands, or proofs within the
theory.
*/

package isabelle


import scala.collection.immutable.SortedMap
import scala.collection.mutable


object Thy_Conditions {
  /** predicates via Isabelle/Scala services **/

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



  /** concrete syntax for conditions **/

  object Token {
    object Kind extends Enumeration {
      val SPACE = Value("white space")
      val KEYWORD = Value("keyword")
      val IDENT = Value("identifier")
      val VARIABLE = Value("environment variable")
      val STRING = Value("string")
      val CARTOUCHE = Value("text cartouche")
      val BAD = Value("bad input")
    }

    private object Scanners extends Scan.Parsers {
      val space = many1(character(Symbol.is_ascii_blank)) ^^ (x => Token(Kind.SPACE, x))

      val keyword = one(character(Set('(', ',', ')'))) ^^ (x => Token(Kind.KEYWORD, x))

      val id =
        one(character(Symbol.is_ascii_letter)) ~
        many(character(c => Symbol.is_ascii_letter(c) || Symbol.is_ascii_digit(c) || c == '_')) ^^
          { case x ~ y => x + y }
      val ident = id ^^ (x => Token(Kind.IDENT, x))
      val variable = one(character(Set('$'))) ~ id ^^ { case x ~ y => Token(Kind.VARIABLE, x + y) }

      val delimited =
        quoted("\"") ^^ (x => Token(Kind.STRING, x)) |
        cartouche ^^ (x => Token(Kind.CARTOUCHE, x))
      val bad =
        (recover_quoted("\"") | recover_cartouche | one(_ => true)) ^^ (x => Token(Kind.BAD, x))

      def token: Parser[Token] =
        space | (keyword | (ident | (variable | (delimited | bad))))
    }

    def explode(inp: CharSequence, whitespace: Boolean = false): List[Text.Info[Token]] = {
      val toks =
        Scanners.parseAll(Scanners.rep(Scanners.token), Scan.char_reader(inp)) match {
          case Scanners.Success(tokens, _) => tokens
          case _ => error("Unexpected failure of tokenizing input:\n" + inp.toString)
        }

      val result = new mutable.ListBuffer[Text.Info[Token]]
      var offset = 0
      for (tok <- toks) {
        val end_offset = offset + tok.source.length
        if (!tok.is_space || whitespace) {
          result += Text.Info(Text.Range(offset, end_offset), tok)
        }
        offset = end_offset
      }
      result.toList
    }
  }

  sealed case class Token(kind: Token.Kind.Value, source: String) {
    def is_space: Boolean = kind == Token.Kind.SPACE
    def is_keyword: Boolean = kind == Token.Kind.KEYWORD
    def is_keyword(name: String): Boolean = is_keyword && source == name
    def is_bad: Boolean = kind == Token.Kind.BAD

    def content: String =
      if (kind == Token.Kind.VARIABLE) Library.perhaps_unprefix("$", source)
      else if (kind == Token.Kind.STRING) Scan.Parsers.perhaps_quoted_content("\"", source)
      else if (kind == Token.Kind.CARTOUCHE) Scan.Parsers.perhaps_cartouche_content(source)
      else source
  }



  /** system options **/

  object Condition extends Shasum.Special_Entry("condition")

  private val any_option: List[String] = List("condition", "condition_proofs")

  val filter_any_option: Set[String] = any_option.toSet
  val filter_theory_option: Set[String] = Set(any_option(0))
  val filter_proofs_option: Set[String] = Set(any_option(1))



  /** mutable state (or cache) **/

  object State {
    def apply(background: Sessions.Background, options: Options): State = {
      val state = new State
      state.init(background, options)
      state
    }
  }

  final class State private {
    private var immutable: Boolean = false
    private var conditions: Thy_Conditions =
      Thy_Conditions.init(Sessions.background0(""), Options.defaults)

    def make_immutable(): Unit = synchronized { immutable = true }

    def value: Thy_Conditions = synchronized { conditions }
    override def toString: String = value.toString

    def init(init_background: Sessions.Background, init_options: Options): Unit =
      synchronized {
        if (!immutable) {
          conditions = Thy_Conditions.init(init_background, init_options)
        }
      }

    def eval_restrict(
      opts: Options.Update,
      filter: Set[String] = Thy_Conditions.filter_any_option
    ): Thy_Conditions = synchronized {
      val domain = conditions.domain(opts, filter = filter)
      val conditions1 = conditions.evaluate(domain)
      if (immutable && conditions.changed(conditions1)) {
        error("Cannot change immutable theory conditions")
      }
      if (!immutable) { conditions = conditions1 }
      conditions1.restrict(domain)
    }
  }



  /** immutable value **/

  def init(background: Sessions.Background, options: Options): Thy_Conditions =
    new Thy_Conditions(background, options, SortedMap.empty)
}

final class Thy_Conditions private(
  val background: Sessions.Background,
  val options: Options,
  protected val rep: SortedMap[String, Exn.Result[String]]
) {
  def changed(other: Thy_Conditions): Boolean = rep != other.rep

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
        yield Shasum.make(SHA1.digest(b.isEmpty), Thy_Conditions.Condition.make(a))))
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

  def domain(
    opts: Options.Update,
    filter: Set[String] = Thy_Conditions.filter_any_option
  ): List[String] = {
    val options1 = options ++ opts.filter(p => filter(p._1))
    Thy_Conditions.any_option.flatMap(name => space_explode(',', options1.string(name)))
  }

  def restrict(domain: List[String]): Thy_Conditions = {
    val domain_set = domain.toSet
    new Thy_Conditions(background, options, rep.filter(p => domain_set(p._1)))
  }

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

  override def toString: String = {
    val a = if_proper(failed, "failed = " + quote(failed.mkString(",")))
    val b = if_proper(good, "good = " + quote(good.mkString(",")))
    val c = if_proper(bad, "bad = " + quote(bad.mkString(",")))
    List(a, b, c).filterNot(_.isEmpty).mkString("Thy_Conditions(", ", ", ")")
  }
}
