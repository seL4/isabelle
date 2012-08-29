/*  Title:      Pure/System/options.scala
    Author:     Makarius

Stand-alone options with external string representation.
*/

package isabelle


import java.util.Calendar


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
  private case object Unknown extends Type

  case class Opt(typ: Type, value: String, description: String)
  {
    def unknown: Boolean = typ == Unknown
  }


  /* parsing */

  private val OPTION = "option"
  private val OPTIONS = Path.explode("etc/options")
  private val PREFS = Path.explode("$ISABELLE_HOME_USER/etc/preferences")
  private val PREFS_BACKUP = Path.explode("$ISABELLE_HOME_USER/etc/preferences~")

  lazy val options_syntax = Outer_Syntax.init() + ":" + "=" + "--" + (OPTION, Keyword.THY_DECL)
  lazy val prefs_syntax = Outer_Syntax.init() + "="

  object Parser extends Parse.Parser
  {
    val option_name = atom("option name", _.is_xname)
    val option_type = atom("option type", _.is_ident)
    val option_value =
      opt(token("-", tok => tok.is_sym_ident && tok.content == "-")) ~ atom("nat", _.is_nat) ^^
        { case s ~ n => if (s.isDefined) "-" + n else n } |
      atom("option value", tok => tok.is_name || tok.is_float)

    val option_entry: Parser[Options => Options] =
    {
      command(OPTION) ~! (option_name ~ keyword(":") ~ option_type ~
      keyword("=") ~ option_value ~ (keyword("--") ~! text ^^ { case _ ~ x => x } | success(""))) ^^
        { case _ ~ (a ~ _ ~ b ~ _ ~ c ~ d) => (options: Options) => options.declare(a, b, c, d) }
    }

    val prefs_entry: Parser[Options => Options] =
    {
      option_name ~ (keyword("=") ~! option_value) ^^
      { case a ~ (_ ~ b) => (options: Options) => options.add_permissive(a, b) }
    }

    def parse_file(syntax: Outer_Syntax, parser: Parser[Options => Options],
      options: Options, file: Path): Options =
    {
      val toks = syntax.scan(File.read(file))
      val ops =
        parse_all(rep(parser), Token.reader(toks, file.implode)) match {
          case Success(result, _) => result
          case bad => error(bad.toString)
        }
      try { (options /: ops) { case (opts, op) => op(opts) } }
      catch { case ERROR(msg) => error(msg + Position.here(file.position)) }
    }
  }

  def init_defaults(): Options =
  {
    var options = empty
    for {
      dir <- Isabelle_System.components()
      file = dir + OPTIONS if file.is_file
    } { options = Parser.parse_file(options_syntax, Parser.option_entry, options, file) }
    options
  }

  def init(): Options = init_defaults().load_prefs()


  /* encode */

  val encode: XML.Encode.T[Options] = (options => options.encode)


  /* command line entry point */

  def main(args: Array[String])
  {
    Command_Line.tool {
      args.toList match {
        case export_file :: more_options =>
          val options = (Options.init() /: more_options)(_ + _)

          if (export_file == "") java.lang.System.out.println(options.print)
          else File.write(Path.explode(export_file), YXML.string_of_body(options.encode))

          0
        case _ => error("Bad arguments:\n" + cat_lines(args))
      }
    }
  }
}


final class Options private(protected val options: Map[String, Options.Opt] = Map.empty)
{
  override def toString: String = options.iterator.mkString("Options (", ",", ")")

  def print: String =
    cat_lines(options.toList.sortBy(_._1).map({ case (name, opt) =>
      "option " + name + " : " + opt.typ.print + " = " +
        (if (opt.typ == Options.String) quote(opt.value) else opt.value) +
      (if (opt.description == "") "" else "\n  -- " + quote(opt.description)) }))


  /* check */

  private def check_name(name: String): Options.Opt =
    options.get(name) match {
      case Some(opt) if !opt.unknown => opt
      case _ => error("Unknown option " + quote(name))
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


  /* external updates */

  private def check_value(name: String): Options =
  {
    val opt = check_name(name)
    opt.typ match {
      case Options.Bool => bool(name); this
      case Options.Int => int(name); this
      case Options.Real => real(name); this
      case Options.String => string(name); this
      case Options.Unknown => this
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
        val opt = Options.Opt(typ, value, description)
        (new Options(options + (name -> opt))).check_value(name)
    }
  }

  def add_permissive(name: String, value: String): Options =
  {
    if (options.isDefinedAt(name)) this + (name, value)
    else new Options(options + (name -> Options.Opt(Options.Unknown, value, "")))
  }

  def + (name: String, value: String): Options =
  {
    val opt = check_name(name)
    (new Options(options + (name -> opt.copy(value = value)))).check_value(name)
  }

  def + (name: String, opt_value: Option[String]): Options =
  {
    val opt = check_name(name)
    opt_value match {
      case Some(value) => this + (name, value)
      case None if opt.typ == Options.Bool => this + (name, "true")
      case None => error("Missing value for option " + quote(name) + " : " + opt.typ.print)
    }
  }

  def + (str: String): Options =
  {
    str.indexOf('=') match {
      case -1 => this + (str, None)
      case i => this + (str.substring(0, i), str.substring(i + 1))
    }
  }

  def ++ (specs: List[Options.Spec]): Options =
    (this /: specs)({ case (x, (y, z)) => x + (y, z) })


  /* encode */

  def encode: XML.Body =
  {
    val opts =
      for ((name, opt) <- options.toList; if !opt.unknown)
        yield (name, opt.typ.print, opt.value)

    import XML.Encode.{string => str, _}
    list(triple(str, str, str))(opts)
  }


  /* user preferences */

  def load_prefs(): Options =
    if (Options.PREFS.is_file)
      Options.Parser.parse_file(
        Options.prefs_syntax, Options.Parser.prefs_entry, this, Options.PREFS)
    else this

  def save_prefs()
  {
    val defaults = Options.init_defaults()
    val changed =
      (for {
        (name, opt2) <- options.iterator
        opt1 = defaults.options.get(name)
        if (opt1.isEmpty || opt1.get.value != opt2.value)
      } yield (name, opt2.value, if (opt1.isEmpty) "  (* unknown *)" else "")).toList

    val prefs =
      changed.sortBy(_._1)
        .map({ case (x, y, z) => x + " = " + Outer_Syntax.quote_string(y) + z + "\n" }).mkString

    Options.PREFS.file renameTo Options.PREFS_BACKUP.file
    File.write(Options.PREFS,
      "(* generated by Isabelle " + Calendar.getInstance.getTime + " *)\n\n" + prefs)
  }
}
