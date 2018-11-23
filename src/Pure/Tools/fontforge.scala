/*  Title:      Pure/Tools/fontforge.scala
    Author:     Makarius

Support for fontforge and its scripting language: see
/usr/share/doc/fontforge/scripting.html e.g. on Ubuntu Linux installation.
*/

package isabelle


import java.io.{File => JFile}
import java.util.Locale


object Fontforge
{
  /** scripting language **/

  type Script = String


  /* concrete syntax */

  def string(s: String): Script =
  {
    def err(c: Char): Nothing =
      error("Bad character \\u" + String.format(Locale.ROOT, "%04x", new Integer(c)) +
        " in fontforge string " + quote(s))

    val q = if (s.contains('"')) '\'' else '"'

    def escape(c: Char): String =
    {
      if (c == '\u0000' || c == '\r' || c == q) err(c)
      else if (c == '\n') "\\n"
      else if (c == '\\') "\\\\"
      else c.toString
    }

    if (s.nonEmpty && s(0) == '\\') err('\\')
    s.iterator.map(escape(_)).mkString(q.toString, "", q.toString)
  }

  def file_name(path: Path): Script = string(File.standard_path(path))


  /* commands */

  // fonts
  def open(path: Path): Script = "Open(" + file_name(path) +")"
  def generate(path: Path): Script = "Generate(" + file_name(path) +")"
  def set_font_names(
    fontname: String = "",
    family: String = "",
    fullname: String = "",
    weight: String = "",
    copyright: String = "",
    fontversion: String = ""): Script =
  {
    List(fontname, family, fullname, weight, copyright, fontversion).map(string(_)).
      mkString("SetFontNames(", ",", ")")
  }

  // selection
  def select(args: Seq[Int]): Script = "SelectSingletons(" + args.mkString(",") + ")"
  def select_all: Script = "SelectAll()"
  def select_none: Script = "SelectNone()"
  def select_invert: Script = "SelectInvert()"
  def clear: Script = "Clear()"
  def copy: Script = "Copy()"
  def paste: Script = "Paste()"



  /** execute fontforge program **/

  def execute(script: Script, args: String = "", cwd: JFile = null): Process_Result =
    Isabelle_System.with_tmp_file("fontforge")(script_file =>
    {
      File.write(script_file, script)
      Isabelle_System.bash(File.bash_path(Path.explode("$ISABELLE_FONTFORGE")) +
        " -lang=ff -script " + File.bash_path(script_file) + " " + args)
    })

  def font_domain(path: Path, strict: Boolean = false): List[Int] =
  {
    val script = """
i = 0
while (i < CharCnt())
  if (""" + (if (strict) "DrawsSomething" else "WorthOutputting") + """(i)); Print(i); endif
  i = i + 1
endloop
"""
    Library.trim_split_lines(execute(open(path) + script).check.out).
      map(Value.Int.parse)
  }
}
