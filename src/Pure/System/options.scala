/*  Title:      Pure/System/options.scala
    Author:     Makarius

Stand-alone options with external string representation.
*/

package isabelle


object Options
{
  type Spec = (String, Option[String])

  val empty: Options = new Options()


  /* representation */

  sealed abstract class Type
  {
    def print: String = toString.toLowerCase
  }
  private case object Bool extends Type
  private case object Int extends Type
  private case object Real extends Type
  private case object String extends Type

  case class Opt(typ: Type, value: String, description: String)


  /* parsing */

  private object Parser extends Parse.Parser
  {
    val DECLARE = "declare"
    val DEFINE = "define"

    val syntax = Outer_Syntax.empty + ":" + "=" + "--" + DECLARE + DEFINE

    val entry: Parser[Options => Options] =
    {
      val option_name = atom("option name", _.is_xname)
      val option_type = atom("option type", _.is_ident)
      val option_value = atom("option value", tok => tok.is_name || tok.is_float)

      keyword(DECLARE) ~! (option_name ~ keyword(":") ~ option_type ~
      keyword("=") ~ option_value ~ (keyword("--") ~! text ^^ { case _ ~ x => x } | success(""))) ^^
        { case _ ~ (a ~ _ ~ b ~ _ ~ c ~ d) => (options: Options) => options.declare(a, b, c, d) } |
      keyword(DEFINE) ~! (option_name ~ keyword("=") ~ option_value) ^^
        { case _ ~ (a ~ _ ~ b) => (options: Options) => options.define(a, b) }
    }

    def parse_entries(file: Path): List[Options => Options] =
    {
      parse_all(rep(entry), Token.reader(syntax.scan(File.read(file)), file.implode)) match {
        case Success(result, _) => result
        case bad => error(bad.toString)
      }
    }
  }

  private val OPTIONS = Path.explode("etc/options")

  def init(): Options =
  {
    var options = empty
    for {
      dir <- Isabelle_System.components()
      file = dir + OPTIONS if file.is_file
      entry <- Parser.parse_entries(file)
    } {
      try { options = entry(options) }
      catch { case ERROR(msg) => error(msg + Position.str_of(file.position)) }
    }
    options
  }


  /* encode */

  val encode: XML.Encode.T[Options] = (options => options.encode)
}


final class Options private(options: Map[String, Options.Opt] = Map.empty)
{
  override def toString: String = options.iterator.mkString("Options (", ",", ")")


  /* check */

  private def check_name(name: String): Options.Opt =
    options.get(name) match {
      case Some(opt) => opt
      case None => error("Unknown option " + quote(name))
    }

  private def check_type(name: String, typ: Options.Type): Options.Opt =
  {
    val opt = check_name(name)
    if (opt.typ == typ) opt
    else error("Ill-typed option " + quote(name) + " : " + opt.typ.print + " vs. " + typ.print)
  }


  /* basic operations */

  private def put[A](name: String, typ: Options.Type, value: String): Options =
  {
    val opt = check_type(name, typ)
    new Options(options + (name -> opt.copy(value = value)))
  }

  private def get[A](name: String, typ: Options.Type, parse: String => Option[A]): A =
  {
    val opt = check_type(name, typ)
    parse(opt.value) match {
      case Some(x) => x
      case None =>
        error("Malformed value for option " + quote(name) +
          " : " + typ.print + " =\n" + quote(opt.value))
    }
  }


  /* internal lookup and update */

  val bool = new Object
  {
    def apply(name: String): Boolean = get(name, Options.Bool, Properties.Value.Boolean.unapply)
    def update(name: String, x: Boolean): Options =
      put(name, Options.Bool, Properties.Value.Boolean(x))
  }

  val int = new Object
  {
    def apply(name: String): Int = get(name, Options.Int, Properties.Value.Int.unapply)
    def update(name: String, x: Int): Options =
      put(name, Options.Int, Properties.Value.Int(x))
  }

  val real = new Object
  {
    def apply(name: String): Double = get(name, Options.Real, Properties.Value.Double.unapply)
    def update(name: String, x: Double): Options =
      put(name, Options.Real, Properties.Value.Double(x))
  }

  val string = new Object
  {
    def apply(name: String): String = get(name, Options.String, s => Some(s))
    def update(name: String, x: String): Options = put(name, Options.String, x)
  }


  /* external declare and define */

  private def check_value(name: String): Options =
  {
    val opt = check_name(name)
    opt.typ match {
      case Options.Bool => bool(name); this
      case Options.Int => int(name); this
      case Options.Real => real(name); this
      case Options.String => string(name); this
    }
  }

  def declare(name: String, typ_name: String, value: String, description: String = ""): Options =
  {
    options.get(name) match {
      case Some(_) => error("Duplicate declaration of option " + quote(name))
      case None =>
        val typ =
          typ_name match {
            case "bool" => Options.Bool
            case "int" => Options.Int
            case "real" => Options.Real
            case "string" => Options.String
            case _ => error("Unknown type for option " + quote(name) + " : " + quote(typ_name))
          }
        (new Options(options + (name -> Options.Opt(typ, value, description)))).check_value(name)
    }
  }

  def define(name: String, value: String): Options =
  {
    val opt = check_name(name)
    (new Options(options + (name -> opt.copy(value = value)))).check_value(name)
  }

  def define(name: String, opt_value: Option[String]): Options =
  {
    val opt = check_name(name)
    opt_value match {
      case Some(value) => define(name, value)
      case None if opt.typ == Options.Bool => define(name, "true")
      case None => error("Missing value for option " + quote(name) + " : " + opt.typ.print)
    }
  }

  def ++ (specs: List[Options.Spec]): Options =
    (this /: specs)({ case (x, (y, z)) => x.define(y, z) })

  def define_simple(str: String): Options =
  {
    str.indexOf('=') match {
      case -1 => define(str, None)
      case i => define(str.substring(0, i), str.substring(i + 1))
    }
  }


  /* encode */

  def encode: XML.Body =
  {
    import XML.Encode.{string => str, _}
    list(triple(str, str, str))(
      options.toList.map({ case (name, opt) => (name, opt.typ.print, opt.value) }))
  }
}
