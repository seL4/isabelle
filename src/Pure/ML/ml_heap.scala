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
      val l = sha1_prefix.length
      val m = l + SHA1.digest_length
      val n = heap.file.length
      val bs = Bytes.read_slice(heap, offset = n - m)
      if (bs.length == m) {
        val s = bs.text
        if (s.startsWith(sha1_prefix)) Some(SHA1.fake_digest(s.substring(l)))
        else None
      }
      else None
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
