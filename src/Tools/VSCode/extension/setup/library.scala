/*  Title:      Tools/VSCode/extension/setup/library.scala
    Author:     Fabian Huch

Basic library, written in Scala (for JS compilation).
*/

package isabelle.setup

import scala.language.unsafeNulls

import scala.jdk.CollectionConverters._


object Library {
  def quote(s: String): String = "\"" + s + "\""

  def cat_lines(lines: java.lang.Iterable[_ <: CharSequence]): String = String.join("\n", lines)

  def split_lines(str: String): java.util.List[String] =
    (if (str.isEmpty) Nil else str.split("\\n").toList).asJava

  def prefix_lines(prfx: String, str: String): String =
    if (str.isEmpty) str
    else cat_lines((for (line <- split_lines(str).asScala) yield prfx + line).asJava)

  def trim_line(s: String): String =
    if (s.endsWith("\r\n")) s.substring(0, s.length - 2)
    else if (s.endsWith("\r") || s.endsWith("\n")) s.substring(0, s.length - 1)
    else s
}