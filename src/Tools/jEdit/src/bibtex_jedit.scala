/*  Title:      Tools/jEdit/src/bibtex_jedit.scala
    Author:     Makarius

BibTeX support in Isabelle/jEdit.
*/

package isabelle.jedit


import isabelle._


import org.gjt.sp.jedit.Buffer


object Bibtex_JEdit
{
  /* buffer model entries */

  def entries_iterator(): Iterator[(String, Buffer, Text.Offset)] =
    for {
      buffer <- JEdit_Lib.jedit_buffers()
      model <- PIDE.document_model(buffer).iterator
      (name, offset) <- model.bibtex_entries.iterator
    } yield (name, buffer, offset)
}

