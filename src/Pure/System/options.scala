/*  Title:      Pure/System/options.scala
    Author:     Makarius

Stand-alone options with external string representation.
*/

package isabelle


import java.io.File


object Options
{
  abstract class Type
  {
    def print: String = toString.toLowerCase
    def init: String
  }
  case object Bool extends Type { def init = "false" }
  case object Int extends Type { def init = "0" }
  case object Real extends Type { def init = "0.0" }
  case object String extends Type { def init = "" }

  case class Opt(typ: Type, description: String, value: String)

  val empty: Options = new Options()


  /* parsing */

  private object Parser extends Parse.Parser
  {
    val DECLARE = "declare"
    val DEFINE = "define"

    val syntax = Outer_Syntax.empty + ":" + "=" + DECLARE + DEFINE

    val entry: Parser[Options => Options] =
    {
      val option_name = atom("option name", _.is_xname)
      val option_type = atom("option type", _.is_ident)
      val option_value = atom("option value", tok => tok.is_name || tok.is_float)

      keyword(DECLARE) ~! (option_name ~ keyword(":") ~ option_type ~ opt(text)) ^^
        { case _ ~ (x ~ _ ~ y ~ z) => (options: Options) =>
            options.declare(x, y, z.getOrElse("")) } |
      keyword(DEFINE) ~! (option_name ~ keyword("=") ~ option_value) ^^
        { case _ ~ (x ~ _ ~ y) => (options: Options) =>
            options.define(x, y) }
    }

    def parse_entries(file: File): List[Options => Options] =
    {
      val toks = syntax.scan(Standard_System.read_file(file))
      parse_all(rep(entry), Token.reader(toks, file.toString)) match {
        case Success(result, _) => result
        case bad => error(bad.toString)
      }
    }
  }

  val OPTIONS = Path.explode("etc/options")

  def init(): Options =
  {
    var options = empty
    for {
      dir <- Isabelle_System.components()
      file = Isabelle_System.platform_file(dir + OPTIONS)
      if file.isFile
      entry <- Parser.parse_entries(file)
    } {
      try { options = entry(options) }
      catch { case ERROR(msg) => error(msg + " (file " + quote(file.toString) + ")") }
    }
    options
  }
}


final class Options private(options: Map[String, Options.Opt] = Map.empty)
{
  override def toString: String = options.iterator.mkString("Options (", ",", ")")


  /* basic operations */

  private def check_name(name: String): Options.Opt =
    options.get(name) match {
      case Some(opt) => opt
      case None => error("Undeclared option " + quote(name))
    }

  private def check_type(name: String, typ: Options.Type): Options.Opt =
  {
    val opt = check_name(name)
    if (opt.typ == typ) opt
    else error("Ill-typed option " + quote(name) + " : " + opt.typ.print + " vs. " + typ.print)
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

  private def put[A](name: String, typ: Options.Type, value: String): Options =
  {
    val opt = check_type(name, typ)
    new Options(options + (name -> opt.copy(value = value)))
  }




  /* external declare and define */

  def declare(name: String, typ_name: String, description: String = ""): Options =
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
            case _ => error("Malformed type for option " + quote(name) + " : " + quote(typ_name))
          }
        new Options(options + (name -> Options.Opt(typ, description, typ.init)))
    }
  }

  def define(name: String, value: String): Options =
  {
    val opt = check_name(name)
    val result = new Options(options + (name -> opt.copy(value = value)))
    opt.typ match {
      case Options.Bool => result.bool(name); ()
      case Options.Int => result.int(name); ()
      case Options.Real => result.real(name); ()
      case Options.String => result.string(name); ()
    }
    result
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
}
