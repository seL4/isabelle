/*  Title:      Pure/General/xz.scala
    Author:     Makarius

Support for Zstd data compression.
*/

package isabelle


object Zstd {
  lazy val init_jni: Unit = {
    val lib_dir = Path.explode("$ISABELLE_ZSTD_HOME/" + Platform.jvm_platform)
    val lib_file =
      File.find_files(lib_dir.file) match {
        case List(file) => file
        case _ => error("Exactly one file expected in directory " + lib_dir.expand)
      }
    System.load(File.platform_path(lib_file.getAbsolutePath))
    com.github.luben.zstd.util.Native.assumeLoaded()
    assert(com.github.luben.zstd.util.Native.isLoaded())
    Class.forName("com.github.luben.zstd.Zstd")
  }
}
