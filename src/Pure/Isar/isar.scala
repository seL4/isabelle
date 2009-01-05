/*  Title:      Pure/Isar/isar.scala
    Author:     Makarius

Isar document model.
*/

package isabelle


class Isar(isabelle_system: IsabelleSystem, results: EventBus[IsabelleProcess.Result], args: String*)
  extends IsabelleProcess(isabelle_system, results, args: _*)
{
  /* basic editor commands */

  def create_command(id: String, text: String) =
    output_sync("Isar.command " + IsabelleSyntax.encode_string(id) + " " +
      IsabelleSyntax.encode_string(text))

  def insert_command(prev: String, id: String) =
    output_sync("Isar.insert " + IsabelleSyntax.encode_string(prev) + " " +
      IsabelleSyntax.encode_string(id))

  def remove_command(id: String) =
    output_sync("Isar.remove " + IsabelleSyntax.encode_string(id))
}
