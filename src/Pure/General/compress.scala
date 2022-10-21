/*  Title:      Pure/General/compress.scala
    Author:     Makarius

Support for generic data compression.
*/

package isabelle


import org.tukaani.xz.{LZMA2Options, ArrayCache, BasicArrayCache}
import com.github.luben.zstd.{BufferPool, NoPool, RecyclingBufferPool,
  ZstdInputStream, ZstdOutputStream}


object Compress {
  /* options */

  object Options {
    def apply(): Options = Options_XZ()
  }
  sealed abstract class Options
  case class Options_XZ(level: Int = 3) extends Options {
    def make: LZMA2Options = {
      val opts = new LZMA2Options
      opts.setPreset(level)
      opts
    }
  }
  case class Options_Zstd(level: Int = 3) extends Options


  /* cache */

  class Cache private(val xz: ArrayCache, val zstd: BufferPool)

  object Cache {
    def none: Cache = { Zstd.init(); new Cache(ArrayCache.getDummyCache(), NoPool.INSTANCE) }
    def make(): Cache = { Zstd.init(); new Cache(new BasicArrayCache, RecyclingBufferPool.INSTANCE) } // FIXME new pool
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
