/*  Title:      Pure/Tools/fontforge.scala
    Author:     Makarius

Support for fontforge and its scripting language:
https://github.com/fontforge/fontforge/blob/master/fontforge/scripting.c
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


  /* execute process */

  def execute(script: Script, args: String = "", cwd: JFile = null): Process_Result =
    Isabelle_System.with_tmp_file("fontforge")(script_file =>
    {
      File.write(script_file, script)
      Isabelle_System.bash(File.bash_path(Path.explode("$ISABELLE_FONTFORGE")) +
        " -lang=ff -script " + File.bash_path(script_file) + " " + args)
    })
}
