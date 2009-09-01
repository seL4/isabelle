/*  Title:      Pure/Isar/isar_document.scala
    Author:     Makarius

Interactive Isar documents.
*/

package isabelle


object Isar_Document
{
  /* unique identifiers */

  type State_ID = String
  type Command_ID = String
  type Document_ID = String
}


trait Isar_Document extends Isabelle_Process
{
  import Isar_Document._


  /* commands */

  def define_command(id: Command_ID, text: String) {
    output_sync("Isar.define_command " + Isabelle_Syntax.encode_string(id) + " " +
      Isabelle_Syntax.encode_string(text))
  }


  /* documents */

  def begin_document(id: Document_ID, path: String) {
    output_sync("Isar.begin_document " + Isabelle_Syntax.encode_string(id) + " " +
      Isabelle_Syntax.encode_string(path))
  }

  def end_document(id: Document_ID) {
    output_sync("Isar.end_document " + Isabelle_Syntax.encode_string(id))
  }

  def edit_document(old_id: Document_ID, new_id: Document_ID,
      edits: List[(Command_ID, Option[Command_ID])])
  {
    def append_edit(edit: (Command_ID, Option[Command_ID]), result: StringBuilder)
    {
      edit match {
        case (id, None) => Isabelle_Syntax.append_string(id, result)
        case (id, Some(id2)) =>
          Isabelle_Syntax.append_string(id, result)
          result.append(" ")
          Isabelle_Syntax.append_string(id2, result)
      }
    }

    val buf = new StringBuilder(40)
    buf.append("Isar.edit_document ")
    Isabelle_Syntax.append_string(old_id, buf)
    buf.append(" ")
    Isabelle_Syntax.append_string(new_id, buf)
    buf.append(" ")
    Isabelle_Syntax.append_list(append_edit, edits, buf)
    output_sync(buf.toString)
  }
}
