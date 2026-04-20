/*  Title:      Pure/GUI/color_value.scala
    Author:     Makarius

Cached color values.
*/

package isabelle


import java.awt.Color


object Color_Value {
  private var cache = Map.empty[String, Color]

  def parse(s: String): Color = {
    val i = java.lang.Long.parseLong(s, 16)
    val r = ((i >> 24) & 0xFF).toInt
    val g = ((i >> 16) & 0xFF).toInt
    val b = ((i >> 8) & 0xFF).toInt
    val a = (i & 0xFF).toInt
    new Color(r, g, b, a)
  }

  def print(c: Color): String = {
    val r = Value.Int.obj(c.getRed)
    val g = Value.Int.obj(c.getGreen)
    val b = Value.Int.obj(c.getBlue)
    val a = Value.Int.obj(c.getAlpha)
    Word.uppercase(Library.format("%02x%02x%02x%02x", r, g, b, a))
  }

  def apply(s: String): Color =
    synchronized {
      cache.get(s) match {
        case Some(c) => c
        case None =>
          val c = parse(s)
          cache += (s -> c)
          c
      }
    }

  def option(options: Options, name: String): Color =
    apply(options.string(name + Options.theme_suffix()))
}
