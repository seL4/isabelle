/*  Title:      Pure/General/compress.scala
    Author:     Makarius

Support for generic data compression.
*/

package isabelle


import org.tukaani.xz
import com.github.luben.zstd


object Compress {
  /* options */

  object Options {
    def apply(): Options = Options_Zstd()
  }
  sealed abstract class Options
  case class Options_XZ(level: Int = 3) extends Options {
    def make: xz.LZMA2Options = {
      val opts = new xz.LZMA2Options
      opts.setPreset(level)
      opts
    }
  }
  case class Options_Zstd(level: Int = 3) extends Options


  /* cache */

  class Cache private(val for_xz: xz.ArrayCache, val for_zstd: zstd.BufferPool)

  object Cache {
    def none: Cache = {
      Zstd.init()
      new Cache(xz.ArrayCache.getDummyCache(), zstd.NoPool.INSTANCE)
  }
    def make(): Cache = {
      Zstd.init()
      val pool = Untyped.constructor(classOf[zstd.RecyclingBufferPool]).newInstance()
      new Cache(new xz.BasicArrayCache, pool)
    }
  }


  /* Scala functions in ML */

  object XZ_Compress extends Scala.Fun_Bytes("XZ.compress") {
    val here = Scala_Project.here
    def apply(arg: Bytes): Bytes = arg.compress(Options_XZ())
  }

  object XZ_Uncompress extends Scala.Fun_Bytes("XZ.uncompress") {
    val here = Scala_Project.here
    def apply(arg: Bytes): Bytes = arg.uncompress_xz()
  }

  object Zstd_Compress extends Scala.Fun_Bytes("Zstd.compress") {
    val here = Scala_Project.here
    def apply(arg: Bytes): Bytes = arg.compress(Options_Zstd())
  }

  object Zstd_Uncompress extends Scala.Fun_Bytes("Zstd.uncompress") {
    val here = Scala_Project.here
    def apply(arg: Bytes): Bytes = arg.uncompress_zstd()
  }
}
