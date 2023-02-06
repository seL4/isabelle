/*  Title:      Pure/ML/ml_heap.scala
    Author:     Makarius

ML heap operations.
*/

package isabelle


import java.nio.ByteBuffer
import java.nio.channels.FileChannel
import java.nio.file.StandardOpenOption


object ML_Heap {
  /** heap file with SHA1 digest **/

  private val sha1_prefix = "SHA1:"

  def read_digest(heap: Path): Option[SHA1.Digest] = {
    if (heap.is_file) {
      using(FileChannel.open(heap.java_path, StandardOpenOption.READ)) { file =>
        val len = file.size
        val n = sha1_prefix.length + SHA1.digest_length
        if (len >= n) {
          file.position(len - n)

          val buf = ByteBuffer.allocate(n)
          var i = 0
          var m = 0
          while ({
            m = file.read(buf)
            if (m != -1) i += m
            m != -1 && n > i
          }) ()

          if (i == n) {
            val prefix = new String(buf.array(), 0, sha1_prefix.length, UTF8.charset)
            val s = new String(buf.array(), sha1_prefix.length, SHA1.digest_length, UTF8.charset)
            if (prefix == sha1_prefix) Some(SHA1.fake_digest(s)) else None
          }
          else None
        }
        else None
      }
    }
    else None
  }

  def write_digest(heap: Path): SHA1.Digest =
    read_digest(heap) getOrElse {
      val digest = SHA1.digest(heap)
      File.append(heap, sha1_prefix + digest.toString)
      digest
    }
}
