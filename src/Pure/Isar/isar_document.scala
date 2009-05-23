/*  Title:      Pure/Isar/isar_document.scala
    Author:     Makarius

Interactive Isar documents.
*/

package isabelle

object IsarDocument {
  /* unique identifiers */

  type State_ID = String
  type Command_ID = String
  type Document_ID = String
}

trait IsarDocument extends IsabelleProcess
{
  import IsarDocument._


  /* commands */

  def define_command(id: Command_ID, text: String) {
    output_sync("Isar.define_command " + IsabelleSyntax.encode_string(id) + " " +
      IsabelleSyntax.encode_string(text))
  }


  /* documents */

  def begin_document(id: Document_ID, path: String) {
    output_sync("Isar.begin_document " + IsabelleSyntax.encode_string(id) + " " +
      IsabelleSyntax.encode_string(path))
  }

  def end_document(id: Document_ID) {
    output_sync("Isar.end_document " + IsabelleSyntax.encode_string(id))
  }

  def edit_document(old_id: Document_ID, new_id: Document_ID,
      edits: List[(Command_ID, Option[Command_ID])])
  {
    def append_edit(edit: (Command_ID, Option[Command_ID]), result: StringBuilder)
    {
      edit match {
        case (id, None) => IsabelleSyntax.append_string(id, result)
        case (id, Some(id2)) =>
          IsabelleSyntax.append_string(id, result)
          result.append(" ")
          IsabelleSyntax.append_string(id2, result)
      }
    }

    val buf = new StringBuilder(40)
    buf.append("Isar.edit_document ")
    IsabelleSyntax.append_string(old_id, buf)
    buf.append(" ")
    IsabelleSyntax.append_string(new_id, buf)
    buf.append(" ")
    IsabelleSyntax.append_list(append_edit, edits, buf)
    output_sync(buf.toString)
  }
}
