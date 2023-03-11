/*  Title:      Pure/System/options.scala
    Author:     Makarius

System options with external string representation.
*/

package isabelle


object Options {
  type Spec = (String, Option[String])

  val empty: Options = new Options()


  /* typed access */

  abstract class Access[A](val options: Options) {
    def apply(name: String): A
    def update(name: String, x: A): Options
    def change(name: String, f: A => A): Options = update(name, f(apply(name)))
  }

  class Access_Variable[A](
    val options: Options_Variable,
    val pure_access: Options => Access[A]
  ) {
    def apply(name: String): A = pure_access(options.value)(name)
    def update(name: String, x: A): Unit =
      options.change(options => pure_access(options).update(name, x))
    def change(name: String, f: A => A): Unit = update(name, f(apply(name)))
  }


  /* representation */

  sealed abstract class Type {
    def print: String = Word.lowercase(toString)
  }
  case object Bool extends Type
  case object Int extends Type
  case object Real extends Type
  case object String extends Type
  case object Unknown extends Type

  val TAG_CONTENT = "content"
  val TAG_DOCUMENT = "document"
  val TAG_BUILD = "build"
  val TAG_UPDATE = "update"
  val TAG_CONNECTION = "connection"

  case class Entry(
    public: Boolean,
    pos: Position.T,
    name: String,
    typ: Type,
    value: String,
    default_value: String,
    standard_value: Option[String],
    tags: List[String],
    description: String,
    section: String
  ) {
    private def print_value(x: String): String = if (typ == Options.String) quote(x) else x
    private def print_standard: String =
      standard_value match {
        case None => ""
        case Some(s) if s == default_value => " (standard)"
        case Some(s) => " (standard " + print_value(s) + ")"
      }
    private def print(default: Boolean): String = {
      val x = if (default) default_value else value
      "option " + name + " : " + typ.print + " = " + print_value(x) + print_standard +
        if_proper(description, "\n  -- " + quote(description))
    }

    def print: String = print(false)
    def print_default: String = print(true)

    def title(strip: String = ""): String = {
      val words = Word.explode('_', name)
      val words1 =
        words match {
          case word :: rest if word == strip => rest
          case _ => words
        }
      Word.implode(words1.map(Word.perhaps_capitalize))
    }
    def title_jedit: String = title("jedit")

    def unknown: Boolean = typ == Unknown

    def has_tag(tag: String): Boolean = tags.contains(tag)

    def session_content: Boolean =
      has_tag(TAG_CONTENT) ||
      has_tag(TAG_DOCUMENT) ||
      has_tag(TAG_UPDATE)
  }


  /* parsing */

  private val SECTION = "section"
  private val PUBLIC = "public"
  private val OPTION = "option"
  private val STANDARD = "standard"
  private val FOR = "for"
  private val OPTIONS = Path.explode("etc/options")
  private val PREFS = Path.explode("$ISABELLE_HOME_USER/etc/preferences")

  val options_syntax: Outer_Syntax =
    Outer_Syntax.empty + ":" + "=" + "--" + "(" + ")" +
      Symbol.comment + Symbol.comment_decoded +
      (SECTION, Keyword.DOCUMENT_HEADING) +
      (PUBLIC, Keyword.BEFORE_COMMAND) +
      (OPTION, Keyword.THY_DECL) +
      STANDARD + FOR

  val prefs_syntax: Outer_Syntax = Outer_Syntax.empty + "="

  trait Parsers extends Parse.Parsers {
    val option_name: Parser[String] = atom("option name", _.is_name)
    val option_type: Parser[String] = atom("option type", _.is_name)
    val option_value: Parser[String] =
      opt(token("-", tok => tok.is_sym_ident && tok.content == "-")) ~ atom("nat", _.is_nat) ^^
        { case s ~ n => if (s.isDefined) "-" + n else n } |
      atom("option value", tok => tok.is_name || tok.is_float)
    val option_standard: Parser[Option[String]] =
      $$$("(") ~! $$$(STANDARD) ~ opt(option_value) ~ $$$(")") ^^ { case _ ~ _ ~ a ~ _ => a }
    val option_tag: Parser[String] = atom("option tag", _.is_name)
    val option_tags: Parser[List[String]] =
      $$$(FOR) ~! rep(option_tag) ^^ { case _ ~ x => x } | success(Nil)
  }

  private object Parsers extends Parsers {
    def comment_marker: Parser[String] =
      $$$("--") | $$$(Symbol.comment) | $$$(Symbol.comment_decoded)

    val option_entry: Parser[Options => Options] = {
      command(SECTION) ~! text ^^
        { case _ ~ a => (options: Options) => options.set_section(a) } |
      opt($$$(PUBLIC)) ~ command(OPTION) ~! (position(option_name) ~ $$$(":") ~ option_type ~
      $$$("=") ~ option_value ~ opt(option_standard) ~ option_tags ~
        (comment_marker ~! text ^^ { case _ ~ x => x } | success(""))) ^^
        { case a ~ _ ~ ((b, pos) ~ _ ~ c ~ _ ~ d ~ e ~ f ~ g) =>
            (options: Options) => options.declare(a.isDefined, pos, b, c, d, e, f, g) }
    }

    val prefs_entry: Parser[Options => Options] = {
      option_name ~ ($$$("=") ~! option_value) ^^
      { case a ~ (_ ~ b) => (options: Options) => options.add_permissive(a, b) }
    }

    def parse_file(
      options: Options,
      file_name: String,
      content: String,
      syntax: Outer_Syntax = options_syntax,
      parser: Parser[Options => Options] = option_entry
    ): Options = {
      val toks = Token.explode(syntax.keywords, content)
      val ops =
        parse_all(rep(parser), Token.reader(toks, Token.Pos.file(file_name))) match {
          case Success(result, _) => result
          case bad => error(bad.toString)
        }
      try { ops.foldLeft(options.set_section("")) { case (opts, op) => op(opts) } }
      catch { case ERROR(msg) => error(msg + Position.here(Position.File(file_name))) }
    }

    def parse_prefs(options: Options, content: String): Options =
      parse_file(options, PREFS.file_name, content, syntax = prefs_syntax, parser = prefs_entry)
  }

  def read_prefs(file: Path = PREFS): String =
    if (file.is_file) File.read(file) else ""

  def init(prefs: String = read_prefs(PREFS), opts: List[String] = Nil): Options = {
    var options = empty
    for {
      dir <- Components.directories()
      file = dir + OPTIONS if file.is_file
    } { options = Parsers.parse_file(options, file.implode, File.read(file)) }
    opts.foldLeft(Parsers.parse_prefs(options, prefs))(_ + _)
  }


  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("options", "print Isabelle system options",
    Scala_Project.here,
    { args =>
      var build_options = false
      var get_option = ""
      var list_options = false
      var export_file = ""

      val getopts = Getopts("""
Usage: isabelle options [OPTIONS] [MORE_OPTIONS ...]

  Options are:
    -b           include $ISABELLE_BUILD_OPTIONS
    -g OPTION    get value of OPTION
    -l           list options
    -x FILE      export options to FILE in YXML format

  Report Isabelle system options, augmented by MORE_OPTIONS given as
  arguments NAME=VAL or NAME.
""",
        "b" -> (_ => build_options = true),
        "g:" -> (arg => get_option = arg),
        "l" -> (_ => list_options = true),
        "x:" -> (arg => export_file = arg))

      val more_options = getopts(args)
      if (get_option == "" && !list_options && export_file == "") getopts.usage()

      val options = {
        val options0 = Options.init()
        val options1 =
          if (build_options)
            Word.explode(Isabelle_System.getenv("ISABELLE_BUILD_OPTIONS")).foldLeft(options0)(_ + _)
          else options0
        more_options.foldLeft(options1)(_ + _)
      }

      if (get_option != "")
        Output.writeln(options.check_name(get_option).value, stdout = true)

      if (export_file != "")
        File.write(Path.explode(export_file), YXML.string_of_body(options.encode))

      if (get_option == "" && export_file == "")
        Output.writeln(options.print, stdout = true)
    })
}


final class Options private(
  options: Map[String, Options.Entry] = Map.empty,
  val section: String = ""
) {
  def iterator: Iterator[Options.Entry] = options.valuesIterator

  override def toString: String = iterator.mkString("Options(", ",", ")")

  private def print_entry(opt: Options.Entry): String =
    if (opt.public) "public " + opt.print else opt.print

  def print: String = cat_lines(iterator.toList.sortBy(_.name).map(print_entry))

  def description(name: String): String = check_name(name).description


  /* check */

  def get(name: String): Option[Options.Entry] = options.get(name)

  def check_name(name: String): Options.Entry =
    get(name) match {
      case Some(opt) if !opt.unknown => opt
      case _ => error("Unknown option " + quote(name))
    }

  private def check_type(name: String, typ: Options.Type): Options.Entry = {
    val opt = check_name(name)
    if (opt.typ == typ) opt
    else error("Ill-typed option " + quote(name) + " : " + opt.typ.print + " vs. " + typ.print)
  }


  /* basic operations */

  private def put(name: String, typ: Options.Type, value: String): Options = {
    val opt = check_type(name, typ)
    new Options(options + (name -> opt.copy(value = value)), section)
  }

  private def get[A](name: String, typ: Options.Type, parse: String => Option[A]): A = {
    val opt = check_type(name, typ)
    parse(opt.value) match {
      case Some(x) => x
      case None =>
        error("Malformed value for option " + quote(name) +
          " : " + typ.print + " =\n" + quote(opt.value))
    }
  }


  /* internal lookup and update */

  val bool: Options.Access[Boolean] =
    new Options.Access[Boolean](this) {
      def apply(name: String): Boolean = get(name, Options.Bool, Value.Boolean.unapply)
      def update(name: String, x: Boolean): Options = put(name, Options.Bool, Value.Boolean(x))
    }

  val int: Options.Access[Int] =
    new Options.Access[Int](this) {
      def apply(name: String): Int = get(name, Options.Int, Value.Int.unapply)
      def update(name: String, x: Int): Options = put(name, Options.Int, Value.Int(x))
    }

  val real: Options.Access[Double] =
    new Options.Access[Double](this) {
      def apply(name: String): Double = get(name, Options.Real, Value.Double.unapply)
      def update(name: String, x: Double): Options = put(name, Options.Real, Value.Double(x))
    }

  val string: Options.Access[String] =
    new Options.Access[String](this) {
      def apply(name: String): String = get(name, Options.String, Some(_))
      def update(name: String, x: String): Options = put(name, Options.String, x)
    }

  def proper_string(name: String): Option[String] =
    Library.proper_string(string(name))

  def seconds(name: String): Time = Time.seconds(real(name))


  /* external updates */

  private def check_value(name: String): Options = {
    val opt = check_name(name)
    opt.typ match {
      case Options.Bool => bool(name); this
      case Options.Int => int(name); this
      case Options.Real => real(name); this
      case Options.String => string(name); this
      case Options.Unknown => this
    }
  }

  def declare(
    public: Boolean,
    pos: Position.T,
    name: String,
    typ_name: String,
    value: String,
    standard: Option[Option[String]],
    tags: List[String],
    description: String
  ): Options = {
    get(name) match {
      case Some(other) =>
        error("Duplicate declaration of option " + quote(name) + Position.here(pos) +
          Position.here(other.pos))
      case None =>
        val typ =
          typ_name match {
            case "bool" => Options.Bool
            case "int" => Options.Int
            case "real" => Options.Real
            case "string" => Options.String
            case _ =>
              error("Unknown type for option " + quote(name) + " : " + quote(typ_name) +
                Position.here(pos))
          }
        val standard_value =
          standard match {
            case None => None
            case Some(_) if typ == Options.Bool =>
              error("Illegal standard value for option " + quote(name) + " : " + typ_name +
                Position.here)
            case Some(s) => Some(s.getOrElse(value))
          }
        val opt =
          Options.Entry(
            public, pos, name, typ, value, value, standard_value, tags, description, section)
        (new Options(options + (name -> opt), section)).check_value(name)
    }
  }

  def add_permissive(name: String, value: String): Options = {
    if (options.isDefinedAt(name)) this + (name, value)
    else {
      val opt =
        Options.Entry(false, Position.none, name, Options.Unknown, value, value, None, Nil, "", "")
      new Options(options + (name -> opt), section)
    }
  }

  def + (name: String, value: String): Options = {
    val opt = check_name(name)
    (new Options(options + (name -> opt.copy(value = value)), section)).check_value(name)
  }

  def + (name: String, opt_value: Option[String]): Options = {
    val opt = check_name(name)
    opt_value orElse opt.standard_value match {
      case Some(value) => this + (name, value)
      case None if opt.typ == Options.Bool => this + (name, "true")
      case None => error("Missing value for option " + quote(name) + " : " + opt.typ.print)
    }
  }

  def + (str: String): Options =
    str match {
      case Properties.Eq(a, b) => this + (a, b)
      case _ => this + (str, None)
    }

  def ++ (specs: List[Options.Spec]): Options =
    specs.foldLeft(this) { case (x, (y, z)) => x + (y, z) }


  /* sections */

  def set_section(new_section: String): Options =
    new Options(options, new_section)

  def sections: List[(String, List[Options.Entry])] =
    options.groupBy(_._2.section).toList.map({ case (a, opts) => (a, opts.toList.map(_._2)) })


  /* encode */

  def encode: XML.Body = {
    val opts =
      for ((_, opt) <- options.toList; if !opt.unknown)
        yield (opt.pos, (opt.name, (opt.typ.print, opt.value)))

    import XML.Encode.{string => string_, _}
    list(pair(properties, pair(string_, pair(string_, string_))))(opts)
  }


  /* changed options */

  def changed(defaults: Options = Options.init(prefs = "")): List[String] =
    (for {
      (name, opt2) <- options.iterator
      opt1 = defaults.get(name)
      if opt1.isEmpty || opt1.get.value != opt2.value
    } yield (name, opt2.value)).toList.sortBy(_._1).map({ case (x, y) => Properties.Eq(x, y) })


  /* save preferences */

  def make_prefs(
    defaults: Options = Options.init(prefs = ""),
    filter: Options.Entry => Boolean = _ => true
  ): String = {
    (for {
      (name, opt2) <- options.iterator
      opt1 = defaults.get(name)
      if (opt1.isEmpty || opt1.get.value != opt2.value) && filter(opt2)
    } yield (name, opt2.value, if (opt1.isEmpty) "  (* unknown *)" else ""))
      .toList.sortBy(_._1)
      .map({ case (x, y, z) => x + " = " + Outer_Syntax.quote_string(y) + z + "\n" }).mkString
  }

  def save_prefs(file: Path = Options.PREFS, defaults: Options = Options.init(prefs = "")): Unit = {
    val prefs = make_prefs(defaults = defaults)
    Isabelle_System.make_directory(file.dir)
    File.write_backup(file, "(* generated by Isabelle " + Date.now() + " *)\n\n" + prefs)
  }
}


class Options_Variable(init_options: Options) {
  private var _options = init_options

  def value: Options = synchronized { _options }
  def change(f: Options => Options): Unit = synchronized { _options = f(_options) }
  def += (name: String, x: String): Unit = change(options => options + (name, x))

  val bool: Options.Access_Variable[Boolean] =
    new Options.Access_Variable[Boolean](this, _.bool)

  val int: Options.Access_Variable[Int] =
    new Options.Access_Variable[Int](this, _.int)

  val real: Options.Access_Variable[Double] =
    new Options.Access_Variable[Double](this, _.real)

  val string: Options.Access_Variable[String] =
    new Options.Access_Variable[String](this, _.string)

  def proper_string(name: String): Option[String] =
    Library.proper_string(string(name))

  def seconds(name: String): Time = value.seconds(name)
}
