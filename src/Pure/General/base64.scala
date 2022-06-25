/*  Title:      Pure/General/base64.scala
    Author:     Makarius

Support for Base64 data encoding.
*/

package isabelle


object Base64 {
  def encode(a: Array[Byte]): String = java.util.Base64.getEncoder.encodeToString(a)
  def decode(s: String): Array[Byte] = java.util.Base64.getDecoder.decode(s)


  /* Scala functions in ML */

  object Decode extends Scala.Fun_Bytes("Base64.decode") {
    val here = Scala_Project.here
    def apply(arg: Bytes): Bytes = Bytes.decode_base64(arg.text)
  }

  object Encode extends Scala.Fun_Bytes("Base64.encode") {
    val here = Scala_Project.here
    def apply(arg: Bytes): Bytes = Bytes(arg.encode_base64)
  }
}
