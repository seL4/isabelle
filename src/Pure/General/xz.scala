/*  Title:      Pure/General/xz.scala
    Author:     Makarius

Support for XZ data compression.
*/

package isabelle


import org.tukaani.xz.{LZMA2Options, ArrayCache, BasicArrayCache}


object XZ
{
  /* options */

  type Options = LZMA2Options

  def options(preset: Int = 3): Options =
  {
    val opts = new LZMA2Options
    opts.setPreset(preset)
    opts
  }


  /* cache */

  type Cache = ArrayCache

  def cache(): ArrayCache = ArrayCache.getDefaultCache()
  def make_cache(): ArrayCache = new BasicArrayCache
}
