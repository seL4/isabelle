/*  Title:      Pure/Isar/isar_document.scala
    Author:     Makarius

Interactive Isar documents.
*/

package isabelle


object Isar_Document
{
  /* protocol messages */

  object Assign {
    def unapply(msg: XML.Tree): Option[List[XML.Tree]] =
      msg match {
        case XML.Elem(Markup.Assign, edits) => Some(edits)
        case _ => None
      }
  }

  object Edit {
    def unapply(msg: XML.Tree): Option[(Document.Command_ID, Document.State_ID)] =
      msg match {
        case XML.Elem(Markup(Markup.EDIT, List((Markup.ID, cmd_id), (Markup.STATE, state_id))), Nil) =>
          Some(cmd_id, state_id)
        case _ => None
      }
  }
}


trait Isar_Document extends Isabelle_Process
{
  import Isar_Document._


  /* commands */

  def define_command(id: Document.Command_ID, text: String) {
    output_sync("Isar.define_command " + Isabelle_Syntax.encode_string(id) + " " +
      Isabelle_Syntax.encode_string(text))
  }


  /* documents */

  def edit_document(old_id: Document.Version_ID, new_id: Document.Version_ID,
      edits: List[Document.Edit[Document.Command_ID]])
  {
    def append_edit(
        edit: (Option[Document.Command_ID], Option[Document.Command_ID]), result: StringBuilder)
    {
      Isabelle_Syntax.append_string(edit._1 getOrElse Document.NO_ID, result)
      edit._2 match {
        case None =>
        case Some(id2) =>
          result.append(" ")
          Isabelle_Syntax.append_string(id2, result)
      }
    }

    def append_node_edit(
        edit: (String, Option[List[(Option[Document.Command_ID], Option[Document.Command_ID])]]),
        result: StringBuilder)
    {
      Isabelle_Syntax.append_string(edit._1, result)
      edit._2 match {
        case None =>
        case Some(eds) =>
          result.append(" ")
          Isabelle_Syntax.append_list(append_edit, eds, result)
      }
    }

    val buf = new StringBuilder(40)
    buf.append("Isar.edit_document ")
    Isabelle_Syntax.append_string(old_id, buf)
    buf.append(" ")
    Isabelle_Syntax.append_string(new_id, buf)
    buf.append(" ")
    Isabelle_Syntax.append_list(append_node_edit, edits, buf)
    output_sync(buf.toString)
  }
}
