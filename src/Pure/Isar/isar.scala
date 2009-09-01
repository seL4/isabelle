/*  Title:      Pure/Isar/isar.scala
    Author:     Makarius

Isar document model.
*/

package isabelle

import scala.actors.Actor


class Isar(isabelle_system: Isabelle_System, receiver: Actor, args: String*)
  extends Isabelle_Process(isabelle_system, receiver, args: _*)
{
  /* basic editor commands */

  def create_command(id: String, text: String) =
    output_sync("Isar.command " + Isabelle_Syntax.encode_string(id) + " " +
      Isabelle_Syntax.encode_string(text))

  def insert_command(prev: String, id: String) =
    output_sync("Isar.insert " + Isabelle_Syntax.encode_string(prev) + " " +
      Isabelle_Syntax.encode_string(id))

  def remove_command(id: String) =
    output_sync("Isar.remove " + Isabelle_Syntax.encode_string(id))
}
