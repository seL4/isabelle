/*  Title:      Pure/System/options.scala
    Author:     Makarius

System options with external string representation.
*/

package isabelle


object Options {
  val empty: Options = new Options()

  object Spec {
    val syntax: Outer_Syntax = Outer_Syntax.empty + "=" + ","

    def parse(content: String): List[Spec] = {
      val parser = Parsers.repsep(Parsers.option_spec, Parsers.$$$(","))
      val reader = Token.reader(Token.explode(syntax.keywords, content), Token.Pos.none)
      Parsers.parse_all(parser, reader) match {
        case Parsers.Success(result, _) => result
        case bad => error(bad.toString)
      }
    }

    def eq(a: String, b: String, permissive: Boolean = false): Spec =
      Spec(a, value = Some(b), permissive = permissive)

    def make(s: String): Spec =
      s match {
        case Properties.Eq(a, b) => eq(a, b)
        case _ => Spec(s)
      }

    def ISABELLE_BUILD_OPTIONS: List[Spec] =
      Word.explode(Isabelle_System.getenv("ISABELLE_BUILD_OPTIONS")).map(make)

    def print_value(s: String): String =
      s match {
        case Value.Boolean(_) => s
        case Value.Long(_) => s
        case Value.Double(_) => s
        case _ => Token.quote_name(syntax.keywords, s)
      }

    def print(name: String, value: String): String = Properties.Eq(name, print_value(value))

    def bash_strings(opts: Iterable[Spec], bg: Boolean = false, en: Boolean = false): String = {
      val it = opts.iterator
      if (it.isEmpty) ""
      else {
        it.map(opt => "-o " + Bash.string(opt.toString))
          .mkString(if (bg) " " else "", " ", if (en) " " else "")
      }
    }
  }

  sealed case class Spec(name: String, value: Option[String] = None, permissive: Boolean = false) {
    override def toString: String = name + if_proper(value, "=" + value.get)
    def print: String =
      value match {
        case None => name
        case Some(v) => Spec.print(name, v)
      }
  }

  sealed case class Change(name: String, value: String, unknown: Boolean) {
    def spec: Spec = Spec.eq(name, value)

    def print_prefs: String =
      name + " = " + Outer_Syntax.quote_string(value) +
        if_proper(unknown, "  (* unknown *)") + "\n"
  }


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

  val TAG_CONTENT = "content"    // formal theory content
  val TAG_DOCUMENT = "document"  // document preparation
  val TAG_BUILD = "build"        // relevant for "isabelle build"
  val TAG_BUILD_SYNC = "build_sync" // relevant for distributed "isabelle build"
  val TAG_UPDATE = "update"      // relevant for "isabelle update"
  val TAG_CONNECTION = "connection"  // private information about connections (password etc.)
  val TAG_COLOR_DIALOG = "color_dialog"  // special color selection dialog
  val TAG_VSCODE = "vscode"      // relevant for "isabelle vscode" and "isabelle vscode_server"

  val SUFFIX_DARK = "_dark"
  def theme_suffix(): String = if (GUI.is_dark_laf()) SUFFIX_DARK else ""

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
      Word.implode(words1.map(Word.perhaps_capitalized))
    }
    def title_jedit: String = title("jedit")

    def unknown: Boolean = typ == Unknown

    def for_tag(tag: String): Boolean = tags.contains(tag)
    def for_content: Boolean = for_tag(TAG_CONTENT)
    def for_document: Boolean = for_tag(TAG_DOCUMENT)
    def for_color_dialog: Boolean = for_tag(TAG_COLOR_DIALOG)
    def for_build_sync: Boolean = for_tag(TAG_BUILD_SYNC)
    def for_vscode: Boolean = for_tag(TAG_VSCODE)

    def is_dark: Boolean = name.endsWith(SUFFIX_DARK)

    def session_content: Boolean = for_content || for_document
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
    val option_spec: Parser[Spec] =
      option_name ~ opt($$$("=") ~! option_value ^^ { case _ ~ x => x }) ^^
        { case x ~ y => Options.Spec(x, value = y) }
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
      { case a ~ (_ ~ b) => (options: Options) =>
          options + Options.Spec.eq(a, b, permissive = true) }
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

  def inline(content: String): Options = Parsers.parse_file(empty, "inline", content)

  def init(prefs: String = read_prefs(file = PREFS), specs: List[Spec] = Nil): Options = {
    var options = empty
    for {
      dir <- Components.directories()
      file = dir + OPTIONS if file.is_file
    } { options = Parsers.parse_file(options, file.implode, File.read(file)) }
    Parsers.parse_prefs(options, prefs) ++ specs
  }

  def init0(): Options = init(prefs = "")


  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("options", "print Isabelle system options",
    Scala_Project.here,
    { args =>
      var build_options = false
      var get_option = ""
      var list_options = false
      var list_tags = List.empty[String]
      var export_file = ""

      val getopts = Getopts("""
Usage: isabelle options [OPTIONS] [MORE_OPTIONS ...]

  Options are:
    -b           include $ISABELLE_BUILD_OPTIONS
    -g OPTION    get value of OPTION
    -l           list options
    -t TAGS      restrict list to given tags (comma-separated)
    -x FILE      export options to FILE in YXML format

  Report Isabelle system options, augmented by MORE_OPTIONS given as
  arguments NAME=VAL or NAME.
""",
        "b" -> (_ => build_options = true),
        "g:" -> (arg => get_option = arg),
        "l" -> (_ => list_options = true),
        "t:" -> (arg => list_tags = space_explode(',', arg)),
        "x:" -> (arg => export_file = arg))

      val more_options = getopts(args)
      if (get_option == "" && !list_options && export_file == "") getopts.usage()

      val options = {
        val options0 = Options.init()
        val options1 =
          if (build_options) options0 ++ Options.Spec.ISABELLE_BUILD_OPTIONS else options0
        more_options.foldLeft(options1)(_ + _)
      }

      if (get_option != "") {
        Output.writeln(options.check_name(get_option).value, stdout = true)
      }

      if (export_file != "") {
        File.write(Path.explode(export_file), YXML.string_of_body(options.encode))
      }

      if (get_option == "" && export_file == "") {
        val filter: Options.Entry => Boolean =
          if (list_tags.isEmpty) (_ => true)
          else opt => list_tags.exists(opt.for_tag)
        Output.writeln(options.print(filter = filter), stdout = true)
      }
    })
}


final class Options private(
  options: Map[String, Options.Entry] = Map.empty,
  val section: String = ""
) {
  def defined(name: String): Boolean = options.isDefinedAt(name)

  def iterator: Iterator[Options.Entry] = options.valuesIterator

  override def toString: String = iterator.mkString("Options(", ",", ")")

  private def print_entry(opt: Options.Entry): String =
    if_proper(opt.public, "public ") + opt.print

  def print(filter: Options.Entry => Boolean = _ => true): String =
    cat_lines(iterator.filter(filter).toList.sortBy(_.name).map(print_entry))

  def description(name: String): String = check_name(name).description

  def spec(name: String): Options.Spec =
    Options.Spec.eq(name, check_name(name).value)


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

  def seconds(name: String): Time = Time.seconds(real(name))

  def threads(default: => Int = Multithreading.num_processors()): Int =
    Multithreading.max_threads(value = int("threads"), default = default)

  def standard_ml(): Options = int.update("threads", threads())


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

  def + (spec: Options.Spec): Options = {
    val name = spec.name
    if (spec.permissive && !defined(name)) {
      val value = spec.value.getOrElse("")
      val opt =
        Options.Entry(false, Position.none, name, Options.Unknown, value, value, None, Nil, "", "")
      new Options(options + (name -> opt), section)
    }
    else {
      val opt = check_name(name)
      def put(value: String): Options =
        (new Options(options + (name -> opt.copy(value = value)), section)).check_value(name)
      spec.value orElse opt.standard_value match {
        case Some(value) => put(value)
        case None if opt.typ == Options.Bool => put("true")
        case None => error("Missing value for option " + quote(name) + " : " + opt.typ.print)
      }
    }
  }

  def + (s: String): Options = this + Options.Spec.make(s)

  def ++ (specs: List[Options.Spec]): Options = specs.foldLeft(this)(_ + _)


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

  def changed(
    defaults: Options = Options.init0(),
    filter: Options.Entry => Boolean = _ => true
  ): List[Options.Change] = {
    List.from(
      for {
        (name, opt2) <- options.iterator
        opt1 = defaults.get(name)
        if (opt1.isEmpty || opt1.get.value != opt2.value) && filter(opt2)
      } yield Options.Change(name, opt2.value, opt1.isEmpty)).sortBy(_.name)
  }


  /* preferences */

  def make_prefs(
    defaults: Options = Options.init0(),
    filter: Options.Entry => Boolean = _ => true
  ): String = changed(defaults = defaults, filter = filter).map(_.print_prefs).mkString

  def save_prefs(file: Path = Options.PREFS, defaults: Options = Options.init0()): Unit = {
    val prefs = make_prefs(defaults = defaults)
    Isabelle_System.make_directory(file.dir)
    File.write_backup(file, "(* generated by Isabelle " + Date.now() + " *)\n\n" + prefs)
  }
}


class Options_Variable(init_options: Options) {
  private var _options = init_options

  def value: Options = synchronized { _options }
  def change(f: Options => Options): Unit = synchronized { _options = f(_options) }
  def += (name: String, x: String): Unit = change(options => options + Options.Spec.eq(name, x))

  val bool: Options.Access_Variable[Boolean] =
    new Options.Access_Variable[Boolean](this, _.bool)

  val int: Options.Access_Variable[Int] =
    new Options.Access_Variable[Int](this, _.int)

  val real: Options.Access_Variable[Double] =
    new Options.Access_Variable[Double](this, _.real)

  val string: Options.Access_Variable[String] =
    new Options.Access_Variable[String](this, _.string)

  def seconds(name: String): Time = value.seconds(name)
}
