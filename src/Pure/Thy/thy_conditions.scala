/*  Title:      Pure/Thy/thy_conditions.scala
    Author:     Makarius

Side-conditions on processing theory body commands, or proofs within the
theory.
*/

package isabelle


import scala.collection.immutable.SortedMap


object Thy_Conditions {
  /** predicates via Isabelle/Scala services **/

  abstract class Predicate(val name: String) {
    override def toString: String = name
    def apply(conditions: Thy_Conditions, args: List[String]): Boolean
  }

  abstract class Predicate0(name: String) extends Predicate(name) {
    override def apply(conditions: Thy_Conditions, args: List[String]): Boolean =
      if (args.isEmpty) apply(conditions)
      else error("empty arguments required")
    def apply(conditions: Thy_Conditions): Boolean
  }

  abstract class Predicate1(name: String) extends Predicate(name) {
    override def apply(conditions: Thy_Conditions, args: List[String]): Boolean =
      args match {
        case List(arg) => apply(conditions, arg)
        case _ => error("single argument required")
      }
    def apply(conditions: Thy_Conditions, arg: String): Boolean
  }

  object Getenv extends Predicate("getenv") {
    def apply(conditions: Thy_Conditions, args: List[String]): Boolean =
      args.forall(a => Isabelle_System.getenv(a).nonEmpty)
  }

  class Predicates(val predicates: Predicate*) extends Isabelle_System.Service

  lazy val predicates: Map[String, Predicate] =
    Isabelle_System.make_services(classOf[Predicates]).flatMap(_.predicates.iterator)
      .foldLeft(Map.empty[String, Predicate])(
        { case (map, pred) =>
            if (map.isDefinedAt(pred.name)) {
              error("Duplicate theory condition predicate: " + quote(pred.name))
            }
            else map + (pred.name -> pred)
        })

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

    private object Scanners extends Scan.Scanners {
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

    def explode(str: String): List[Token] =
      Scanners.parseAll(Scanners.rep(Scanners.token), Scan.char_reader(str)) match {
        case Scanners.Success(tokens, _) => tokens
        case _ => error("Unexpected failure of tokenizing input:\n" + str)
      }
  }

  sealed case class Token(kind: Token.Kind.Value, source: String) extends Position.E {
    def is_proper: Boolean = kind != Token.Kind.SPACE
    def is_keyword: Boolean = kind == Token.Kind.KEYWORD
    def is_keyword(name: String): Boolean = is_keyword && source == name
    def is_ident: Boolean = kind == Token.Kind.IDENT
    def is_variable: Boolean = kind == Token.Kind.VARIABLE
    def is_arg: Boolean = kind == Token.Kind.STRING || kind == Token.Kind.CARTOUCHE
    def is_bad: Boolean = kind == Token.Kind.BAD

    def content: String =
      if (kind == Token.Kind.VARIABLE) Library.perhaps_unprefix("$", source)
      else if (kind == Token.Kind.STRING) Scan.Scanners.perhaps_quoted_content("\"", source)
      else if (kind == Token.Kind.CARTOUCHE) Scan.Scanners.perhaps_cartouche_content(source)
      else source
  }

  object Cond {
    private object Parsers extends Position.Parsers {
      type Elem = Token

      def $$$(name: String): Parser[Token] = proper_elem(name, _.is_keyword(name))

      val arg: Parser[String] = atom("string or cartouche", _.is_arg)
      val args: Parser[List[String]] =
        $$$("(") ~! (repsep(arg, $$$(",")) ~ $$$(")")) ^^ { case _ ~ (a ~ _) => a }

      val cond: Parser[Cond] =
        proper_elem(Token.Kind.VARIABLE.toString, _.is_variable) ^^
          { a => Cond(Getenv.name, args = Some(List(a.content))) } |
        proper_elem(Token.Kind.IDENT.toString, _.is_ident) ~ opt(args) ^^
          { case a ~ b => Cond(a.content, args = b) }

      val conds: Parser[List[Cond]] = repsep(cond, $$$(","))
    }

    def parse(str: String, start: Position.P = Position.P.none): List[Cond] =
      Parsers.parse_all(Parsers.conds, Position.reader(Token.explode(str), start)) match {
        case Parsers.Success(result, _) => result
        case bad => error(bad.toString)
      }

    object Ordering extends scala.math.Ordering[Cond] {
      override def compare(a: Cond, b: Cond): Int = a.string compare b.string
    }
  }

  sealed case class Cond(name: String, args: Option[List[String]] = None) {
    override def toString: String = string
    val string: String =
      args match {
        case None => name
        case Some(as) => name + as.map(Outer_Syntax.quote_string).mkString("(", ", ", ")")
      }

    def evaluate(conditions: Thy_Conditions): String =
      if (args.isDefined) {
        if (Thy_Conditions.the_predicate(name)(conditions, args.get)) "" else "false"
      }
      else {
        val options = conditions.options
        Value.Boolean.unapply(name) match {
          case Some(b) => if (b) "" else "false"
          case None =>
            options.get(name).map(_.typ) match {
              case Some(Options.Bool) => if (options.bool(name)) "" else "false"
              case Some(Options.Int) =>
                options.int(name) match {
                  case x if x > 0 => ""
                  case x if x < 0 => "< 0"
                  case 0 => "0"
                }
              case Some(Options.Real) =>
                options.real(name) compare 0.0 match {
                  case x if x > 0.0 && java.lang.Double.isFinite(x) => ""
                  case x if x < 0.0 && java.lang.Double.isFinite(x) => "< 0"
                  case 0.0 => "0"
                  case x => "ill-defined"
                }
              case Some(Options.String) => if (options.string(name).nonEmpty) "" else "empty"
              case _ =>
                error("Condition " + quote(name) + " cannot be evaluated as system option" +
                  "\n(environment variables need to be given as \"$NAME\")")
            }
        }
      }
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
    new Thy_Conditions(background, options, SortedMap.empty(Cond.Ordering))
}

final class Thy_Conditions private(
  val background: Sessions.Background,
  val options: Options,
  protected val rep: SortedMap[Thy_Conditions.Cond, Exn.Result[String]]
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
        yield Shasum.make(SHA1.digest(b.isEmpty), Thy_Conditions.Condition.make(a.toString))))
  }

  def failed: List[Thy_Conditions.Cond] =
    List.from(for (case (a, Exn.Exn(_)) <- rep.iterator) yield a)
  def good: List[Thy_Conditions.Cond] =
    List.from(for (case (a, Exn.Res("")) <- rep.iterator) yield a)
  def bad: List[Thy_Conditions.Cond] =
    List.from(for (case (a, Exn.Res(b)) <- rep.iterator if b.nonEmpty) yield a)
  def bad_message: String = {
    val bads =
      List.from(
        for (case (a, Exn.Res(b)) <- rep.iterator if b.nonEmpty)
          yield "condition " + a.toString + " is " + b)
    if (bads.isEmpty) "" else bads.mkString("(", ",", ")")
  }

  def domain(
    opts: Options.Update,
    filter: Set[String] = Thy_Conditions.filter_any_option
  ): List[Thy_Conditions.Cond] = {
    val options1 = options ++ opts.filter(p => filter(p._1))
    Thy_Conditions.any_option.flatMap(name => Thy_Conditions.Cond.parse(options1.string(name)))
  }

  def restrict(domain: List[Thy_Conditions.Cond]): Thy_Conditions = {
    val domain_set = domain.toSet
    new Thy_Conditions(background, options, rep.filter(p => domain_set(p._1)))
  }

  def evaluate(cond: Thy_Conditions.Cond): Thy_Conditions =
    if (rep.isDefinedAt(cond)) this
    else {
      val result = Exn.result(cond.evaluate(this))
      new Thy_Conditions(background, options, rep + (cond -> result))
    }

  def evaluate(conds: List[Thy_Conditions.Cond]): Thy_Conditions =
    conds.foldLeft(this)(_ evaluate _)

  override def toString: String = {
    val a = if_proper(failed, "failed = " + quote(failed.mkString(",")))
    val b = if_proper(good, "good = " + quote(good.mkString(",")))
    val c = if_proper(bad, "bad = " + quote(bad.mkString(",")))
    List(a, b, c).filterNot(_.isEmpty).mkString("Thy_Conditions(", ", ", ")")
  }
}

class Predicates extends Thy_Conditions.Predicates(Thy_Conditions.Getenv)
