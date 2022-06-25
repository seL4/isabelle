/*  Title:      Pure/General/xz.scala
    Author:     Makarius

Support for XZ data compression.
*/

package isabelle


import org.tukaani.xz.{LZMA2Options, ArrayCache, BasicArrayCache}


object XZ {
  /* options */

  type Options = LZMA2Options

  def options(preset: Int = 3): Options = {
    val opts = new LZMA2Options
    opts.setPreset(preset)
    opts
  }


  /* cache */

  type Cache = ArrayCache

  object Cache {
    def none: ArrayCache = ArrayCache.getDummyCache()
    def apply(): ArrayCache = ArrayCache.getDefaultCache()
    def make(): ArrayCache = new BasicArrayCache
  }


  /* Scala functions in ML */

  object Compress extends Scala.Fun_Bytes("XZ.compress") {
    val here = Scala_Project.here
    def apply(arg: Bytes): Bytes = arg.compress()
  }

  object Uncompress extends Scala.Fun_Bytes("XZ.uncompress") {
    val here = Scala_Project.here
    def apply(arg: Bytes): Bytes = arg.uncompress()
  }
}
