/*  Title:      Pure/General/xz.scala
    Author:     Makarius

Support for XZ data compression.
*/

package isabelle


import org.tukaani.xz.LZMA2Options


object XZ
{
  type Options = LZMA2Options

  def options(): Options = options_preset(3)

  def options_preset(preset: Int): Options =
  {
    val opts = new LZMA2Options
    opts.setPreset(preset)
    opts
  }
}
