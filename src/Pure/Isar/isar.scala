/*  Title:      Pure/Isar/isar.scala
    Author:     Makarius

Isar toplevel editor model.
*/

package isabelle

import java.util.Properties


class Isar(isabelle_system: IsabelleSystem, args: String*) extends
    IsabelleProcess(isabelle_system, args: _*) {

  /* basic editor commands */

  def create_command(props: Properties, text: String) =
    output_sync("Isar.command " + IsabelleSyntax.encode_properties(props) + " " +
      IsabelleSyntax.encode_string(text))

  def insert_command(prev: String, id: String) =
    output_sync("Isar.insert " + IsabelleSyntax.encode_string(prev) + " " +
      IsabelleSyntax.encode_string(id))

  def remove_command(id: String) =
    output_sync("Isar.remove " + IsabelleSyntax.encode_string(id))

}
