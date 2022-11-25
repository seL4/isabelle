/*  Title:      Pure/General/xz.scala
    Author:     Makarius

Support for Zstd data compression.
*/

package isabelle


import com.github.luben.zstd


object Zstd {
  def init(): Unit = init_jni

  private lazy val init_jni: Unit = {
    require(!zstd.util.Native.isLoaded(),
      "Zstd library already initialized by other means than isabelle.Zstd.init()")

    val lib_dir = Path.explode("$ISABELLE_ZSTD_HOME/" + Platform.jvm_platform)
    val lib_file = File.get_file(lib_dir)

    System.load(lib_file.absolute_file.getPath)

    zstd.util.Native.assumeLoaded()
    assert(zstd.util.Native.isLoaded())
    Class.forName("com.github.luben.zstd.Zstd")
  }
}
