/*  Title:      Pure/General/base64.scala
    Author:     Makarius

Support for Base64 data representation.
*/

package isabelle


import java.io.{InputStream, OutputStream}


object Base64 {
  /* main operations */

  def encode(a: Array[Byte]): String = java.util.Base64.getEncoder.encodeToString(a)
  def decode(s: String): Array[Byte] = java.util.Base64.getDecoder.decode(s)

  def encode_stream(s: OutputStream): OutputStream = java.util.Base64.getEncoder.wrap(s)
  def decode_stream(s: InputStream): InputStream = java.util.Base64.getDecoder.wrap(s)


  /* Scala functions in ML */

  object Decode extends Scala.Fun_Bytes("Base64.decode") {
    val here = Scala_Project.here
    def apply(bytes: Bytes): Bytes = bytes.decode_base64
  }

  object Encode extends Scala.Fun_Bytes("Base64.encode") {
    val here = Scala_Project.here
    def apply(bytes: Bytes): Bytes = bytes.encode_base64
  }
}
