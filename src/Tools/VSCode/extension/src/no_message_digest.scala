/*  Title:      Tools/VSCode/extension/src/no_message_digest.scala
    Author:     Fabian Huch

No message digest builder on browser platform.
*/

package isabelle.platform

import isabelle._


object No_Message_Digest {
  def builder(kind: String): Message_Digest.Builder = error("Unsupported browser platform")
}

val message_digest_provider = No_Message_Digest
