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
    def unapply(msg: XML.Tree): Option[(Document.Command_ID, Document.Exec_ID)] =
      msg match {
        case XML.Elem(Markup(Markup.EDIT, List((Markup.ID, cmd_id), (Markup.STATE, state_id))), Nil) =>
          (Markup.parse_long(cmd_id), Markup.parse_long(state_id)) match {
            case (Some(i), Some(j)) => Some((i, j))
            case _ => None
          }
        case _ => None
      }
  }
}


trait Isar_Document extends Isabelle_Process
{
  import Isar_Document._


  /* commands */

  def define_command(id: Document.Command_ID, text: String): Unit =
    input("Isar_Document.define_command", Document.print_id(id), text)


  /* documents */

  def edit_document(old_id: Document.Version_ID, new_id: Document.Version_ID,
      edits: List[Document.Edit[Document.Command_ID]])
  {
    def make_id1(id1: Option[Document.Command_ID]): XML.Body =
      XML_Data.make_long(id1 getOrElse Document.NO_ID)

    val arg =
      XML_Data.make_list(
        XML_Data.make_pair(XML_Data.make_string)(
          XML_Data.make_option(XML_Data.make_list(
              XML_Data.make_pair(make_id1)(XML_Data.make_option(XML_Data.make_long))))))(edits)

    input("Isar_Document.edit_document",
      Document.print_id(old_id), Document.print_id(new_id), YXML.string_of_body(arg))
  }
}
