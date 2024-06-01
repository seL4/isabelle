/*  Title:      Pure/Tools/fontforge.scala
    Author:     Makarius

Support for fontforge and its scripting language: see
/usr/share/doc/fontforge/scripting.html e.g. on Ubuntu Linux installation.
*/

package isabelle


import java.util.Locale


object Fontforge {
  /** scripting language **/

  type Script = String


  /* concrete syntax */

  def string(s: String): Script = {
    def err(c: Char): Nothing =
      error("Bad character \\u" + String.format(Locale.ROOT, "%04x", Integer.valueOf(c)) +
        " in fontforge string " + quote(s))

    val q = if (s.contains('"')) '\'' else '"'

    def escape(c: Char): String = {
      if (c == '\u0000' || c == '\r' || c == q) err(c)
      else if (c == '\n') "\\n"
      else if (c == '\\') "\\\\"
      else c.toString
    }

    if (s.nonEmpty && s(0) == '\\') err('\\')
    s.iterator.map(escape).mkString(q.toString, "", q.toString)
  }

  def file_name(path: Path): Script = string(File.standard_path(path))


  /* commands */

  def command_list(cmds: List[String]): Script = cat_lines(cmds)
  def commands(cmds: String*): Script = command_list(cmds.toList)

  // fonts
  def open(path: Path): Script = "Open(" + file_name(path) +")"
  def close: Script = "Close()"
  def generate(path: Path): Script = "Generate(" + file_name(path) +")"

  // selection
  def select_all: Script = "SelectAll()"
  def select_none: Script = "SelectNone()"
  def select_invert: Script = "SelectInvert()"
  def select(args: Seq[Int]): Script =
    command_list(select_none :: args.toList.map(code => "SelectMoreSingletons(" + code + ")"))

  def clear: Script = "Clear()"
  def copy: Script = "Copy()"
  def paste: Script = "Paste()"



  /** execute fontforge program **/

  def execute(script: Script, args: String = "", cwd: Path = Path.current): Process_Result =
    Isabelle_System.with_tmp_file("fontforge") { script_file =>
      File.write(script_file, script)
      Isabelle_System.bash(File.bash_path(Path.explode("$ISABELLE_FONTFORGE")) +
        " -lang=ff -script " + File.bash_path(script_file) + " " + args)
    }

  def font_domain(path: Path, strict: Boolean = false): List[Int] = {
    val script =
      commands(
        open(path),
        "i = 0",
        "while (i < CharCnt() && i < 0x110000)",
        "  if (" + (if (strict) "DrawsSomething" else "WorthOutputting") + "(i)); Print(i); endif",
        "  i = i + 1",
        "endloop",
        close)
    Library.trim_split_lines(execute(script).check.out).map(Value.Int.parse)
  }


  /* font names */

  sealed case class Font_Names(
    fontname: String = "",
    familyname: String = "",
    fullname: String = "",
    weight: String = "",
    copyright: String = "",
    fontversion: String = ""
  ) {
    override def toString: String = fontname

    def ttf: Path = Path.explode(fontname).ext("ttf")

    def update(prefix: String = "", version: String = ""): Font_Names = {
      val fontversion1 = proper_string(version) getOrElse fontversion
      if (prefix == "") copy(fontversion = fontversion1)
      else {
        copy(fontname = prefix + fontname,
          familyname = prefix + " " + familyname,
          fullname = prefix + " " + fullname,
          weight = weight,
          copyright = copyright,
          fontversion = fontversion1)
      }
    }

    def set: Script =
      List(fontname, familyname, fullname, weight, copyright, fontversion).map(string).
        mkString("SetFontNames(", ",", ")")
  }

  def font_names(path: Path): Font_Names = {
    val script =
      commands(
        open(path),
        "Print($fontname)",
        "Print($familyname)",
        "Print($fullname)",
        "Print($weight)",
        "Print($fontversion)",
        "Print($copyright)",
        close)
    Library.trim_split_lines(execute(script).check.out) match {
      case fontname :: familyname :: fullname :: weight :: fontversion :: copyright =>
        Font_Names(fontname, familyname, fullname, weight, cat_lines(copyright), fontversion)
      case res => error(cat_lines("Bad font names: " :: res))
    }
  }
}
