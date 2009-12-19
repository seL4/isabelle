/*  Title:      Pure/library.scala
    Author:     Makarius

Basic library.
*/

package isabelle

import java.lang.System


object Library
{
  /* timing */

  def timeit[A](e: => A) =
  {
    val start = System.currentTimeMillis()
    val result = Exn.capture(e)
    val stop = System.currentTimeMillis()
    System.err.println((stop - start) + "ms elapsed time")
    Exn.release(result)
  }
}
